/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <algorithm>
#include <atomic>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <mutex>
#include <new>
#include <shared_mutex>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#if defined(LEAN_MMAP) && (defined(__linux__) || defined(__APPLE__))
#define PAPERLEAN_NATIVE_LIBS
#include <climits>
#include <dlfcn.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#if defined(__linux__)
#include <link.h>
#else
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#endif
#endif
#include "runtime/object.h"
#include "runtime/object_ref.h"
#include "runtime/io.h"
#include "runtime/thread.h"
#include "runtime/exception.h"
#include "runtime/sstream.h"
#include "util/name.h"
#include "paperlean/fast_import.h"
#include "paperlean/olean_pack.h"
#include "paperlean/side_file.h"
#include "paperlean/native_libs.h"

/*
Native libraries of packages: shared libraries compiled from the `.c` files of a package's modules,
prepared locally, each with a manifest (`.paperlean`, kind `native-lib`) that records the library's
file identity and, for every module compiled into it, the identities of the module's files
(`.olean`, `.olean.server`, `.olean.private`, `.ir.sig`, `.ir`) the `.c` file was generated with.
`PAPERLEAN_NATIVE_LIBS` is a `:`-separated list of manifests, dependencies first (on Linux and
macOS).

When `finalizePersistentExtensions` starts, before the interpreter first runs for the environment,
`lean_paperlean_load_native_libs` decides per imported module whether the interpreter uses the
native code of a library for it, as with `--load-dynlib`, or interprets it as without native
libraries. It uses a library's code for a module only if
- an import got the module's data from an olean pack (the data are the root of a packed part of
  the module) and the files the pack recorded for the module, unchanged since packing, are exactly
  those of the manifest;
- the module's initializer resolves into that library, so that its symbols are the library's;
- the initializers that native code runs are those that the interpreter would run, in the same
  order: `runInitAttrForMod` runs the module's runtime initializer (which initializes its
  non-`meta` declarations; then all of its code is used) or only its compile-time initializer
  (which initializes its `meta` declarations; then only these are used); the native initializers
  of a module run the runtime initializers of its direct imports (only of its `meta import`s for
  the compile-time initializer), so these must use all of their code, and come before it in the
  import order if they have `[init]` declarations;
- the same holds for the code that it calls: that of its direct imports (only their `meta`
  declarations through regular imports of a module of which only `meta` code is used, which the
  module system ensures, and which must then come before it), unless that is Lean's own code (Lean's
  own libraries, which Lean always uses for their modules, including those that these libraries
  depend on, such as `libLake_shared`, or a library loaded otherwise, which Lean would use as well).
The interpreter's lookups (`library/ir_interpreter.cpp`) then get an address in these libraries only
for a declaration of such a module, of the library verified for it, and a module initializer only for
such a module of the import being finalized on the thread; other addresses in these libraries, and
in libraries they pulled in that are not Lean's own, are filtered out. A module without native code
is interpreted, with the same results.

Format: `native_header`, then `native_module`s, `native_part`s, the manifests of the libraries it
is linked against (`native_string`s), and the strings; the checksum covers everything after the
header.
*/

namespace lean {
// `Lean.PaperLean.Import`; the arguments are owned
extern "C" obj_res lean_paperlean_env_imports_id(obj_arg env);
extern "C" uint32 lean_paperlean_const_module_idx(obj_arg env, obj_arg n);
extern "C" uint8 lean_paperlean_is_meta_const(obj_arg env, obj_arg n);
extern "C" obj_res lean_paperlean_native_import_info(obj_arg env, obj_arg opts);
extern "C" LEAN_EXPORT obj_res lean_paperlean_load_native_libs(b_obj_arg env, b_obj_arg opts);

namespace {
constexpr char g_native_kind[] = "native-lib";
constexpr uint32_t g_native_format = 3;
constexpr uint64_t g_max_manifest_size = uint64_t(1) << 30;

struct native_string { uint64_t off, len; };
struct native_header {
    side_file_header common;
    uint32_t format, num_modules, num_parts, num_deps;
    uint64_t size;
    file_identity lib;
    native_string lib_path;     // absolute, or relative to the manifest's directory
    uint64_t modules_off, parts_off, deps_off, strings_off, strings_size;
};
struct native_module {
    native_string name;
    uint64_t name_hash;         // `Name.hash`
    uint32_t first_part, num_parts;
    uint32_t flags, unused;     // `native_*`, from its `.c` file
};
// Its runtime initializer runs `[init]` declarations.
constexpr uint32_t native_runtime_init_runs = 1;
// Its compile-time initializer initializes declarations.
constexpr uint32_t native_meta_init_initializes = 2;
// The other flags are known.
constexpr uint32_t native_init_known = 4;
// Its runtime initializer initializes declarations (which `meta` code can use: those generated by
// the compiler belong to both phases).
constexpr uint32_t native_runtime_init_initializes = 8;
// A file of a module; the files of a module are in increasing order of kind.
struct native_part {
    uint32_t kind, unused;      // `module_file_kind`
    file_identity id;
};

uint64_t native_checksum(native_header hdr, char const * body, size_t size) {
    hdr.common.checksum = 0;
    return side_file_checksum(body, size, side_file_checksum(&hdr, sizeof(hdr)));
}

// The imports of the environment being finalized on this thread (`lean_paperlean_env_imports_id`)
// and the module initializers of these libraries that its finalization may run, if it uses any.
struct native_inits {
    lean_object * imports;
    std::unordered_map<std::string, int32_t> * inits;   // the initializer's library
};
LEAN_THREAD_PTR(std::vector<native_inits>, g_finalizing);

lean_object * imports_id(b_obj_arg env) {
    lean_inc(env);
    object * h = lean_paperlean_env_imports_id(env);
    // `env` still holds it
    lean_dec(h);
    return h;
}

#ifdef PAPERLEAN_NATIVE_LIBS
// A library loaded from a manifest, or one of Lean's own libraries that such a library pulled in
// (`toolchain`), which Lean's own code is trusted like.
struct loaded_lib {
    std::string path;           // canonical
    file_identity id;
    bool toolchain;
};
// An address range of a loaded object: of a library of `g_libs`, `g_pulled_in` for another library
// that one of them pulled in, or `g_core` for Lean's own code that was loaded before them, whose
// modules `lean_initialize` initialized.
struct addr_range { uintptr_t lo, hi; int32_t owner; };
constexpr int32_t g_pulled_in = -1;
// for addresses outside these ranges, and initializers that cannot be found
constexpr int32_t g_elsewhere = -2;
constexpr int32_t g_core = -3;
constexpr int32_t g_not_found = -4;

std::shared_mutex g_libs_mutex;
std::vector<loaded_lib> * g_libs = new std::vector<loaded_lib>();
std::vector<addr_range> * g_ranges = new std::vector<addr_range>();   // sorted, disjoint
std::atomic<bool> g_any_loaded{false};
// Per import (`lean_paperlean_env_imports_id`, persistent, so never freed) that uses these
// libraries, per module index, the library whose native code is used for the module, or -1, and
// whether only for its `meta` declarations.
struct native_modules {
    std::vector<int32_t> lib_of;
    std::vector<bool> meta_only;
};
std::unordered_map<lean_object *, native_modules> * g_native_modules = new std::unordered_map<lean_object *, native_modules>();

int32_t owner_of(uintptr_t a) {
    std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
    auto it = std::upper_bound(g_ranges->begin(), g_ranges->end(), a,
                               [](uintptr_t x, addr_range const & r) { return x < r.lo; });
    if (it == g_ranges->begin()) return g_elsewhere;
    --it;
    return a < it->hi ? it->owner : g_elsewhere;
}

// A loaded object: its load bias, name, segments, and whether it is the main program.
struct loaded_object {
    uintptr_t base;
    std::string name;
    std::vector<std::pair<uintptr_t, uintptr_t>> segments;
    bool main_program;
};

#if defined(__linux__)
int collect_object(dl_phdr_info * info, size_t, void * data) {
    auto * out = static_cast<std::vector<loaded_object> *>(data);
    loaded_object o { info->dlpi_addr, info->dlpi_name ? info->dlpi_name : "", {}, false };
    // the main program comes first, without a name
    o.main_program = out->empty() && o.name.empty();
    for (int i = 0; i < info->dlpi_phnum; i++) {
        ElfW(Phdr) const & ph = info->dlpi_phdr[i];
        if (ph.p_type != PT_LOAD || ph.p_memsz == 0) continue;
        uintptr_t lo = info->dlpi_addr + ph.p_vaddr;
        o.segments.push_back({ lo, lo + ph.p_memsz });
    }
    out->push_back(std::move(o));
    return 0;
}

std::vector<loaded_object> loaded_objects() {
    std::vector<loaded_object> out;
    dl_iterate_phdr(collect_object, &out);
    return out;
}
#else
std::vector<loaded_object> loaded_objects() {
    std::vector<loaded_object> out;
    uint32_t count = _dyld_image_count();
    for (uint32_t i = 0; i < count; i++) {
        mach_header const * h = _dyld_get_image_header(i);
        if (!h || h->magic != MH_MAGIC_64) continue;
        char const * name = _dyld_get_image_name(i);
        uintptr_t slide = static_cast<uintptr_t>(_dyld_get_image_vmaddr_slide(i));
        // the main program is image 0
        loaded_object o { slide, name ? name : "", {}, i == 0 };
        auto const * lc = reinterpret_cast<load_command const *>(reinterpret_cast<mach_header_64 const *>(h) + 1);
        for (uint32_t c = 0; c < h->ncmds; c++) {
            if (lc->cmd == LC_SEGMENT_64) {
                auto const * seg = reinterpret_cast<segment_command_64 const *>(lc);
                if (seg->vmsize > 0 && strcmp(seg->segname, SEG_PAGEZERO) != 0)
                    o.segments.push_back({ seg->vmaddr + slide, seg->vmaddr + slide + seg->vmsize });
            }
            lc = reinterpret_cast<load_command const *>(reinterpret_cast<char const *>(lc) + lc->cmdsize);
        }
        out.push_back(std::move(o));
    }
    return out;
}
#endif

bool canonical_path(std::string const & path, std::string & out) {
    char buf[PATH_MAX];
    if (!realpath(path.c_str(), buf)) return false;
    out = buf;
    return true;
}

std::string dir_of(std::string const & path) {
    size_t i = path.rfind('/');
    return i == std::string::npos ? std::string() : path.substr(0, i);
}

// The directory of Lean's own shared libraries (that of this code), canonical.
std::string const & lean_lib_dir() {
    static std::string dir = [] {
        Dl_info info;
        std::string path;
        if (dladdr(reinterpret_cast<void *>(&lean_paperlean_load_native_libs), &info) && info.dli_fname &&
            canonical_path(info.dli_fname, path))
            return dir_of(path);
        return std::string();
    }();
    return dir;
}

void add_ranges(std::vector<addr_range> const & ranges) {
    g_ranges->insert(g_ranges->end(), ranges.begin(), ranges.end());
    std::sort(g_ranges->begin(), g_ranges->end(), [](addr_range const & a, addr_range const & b) { return a.lo < b.lo; });
}

bool is_lean_lib(std::string const & name, std::string & path) {
    return !lean_lib_dir().empty() && canonical_path(name, path) && dir_of(path) == lean_lib_dir();
}

// Records the ranges of Lean's own code before the first library is loaded (`g_libs_mutex` held):
// the main program and its libraries `libInit_shared` and `libleanshared*`.
void note_core() {
    static bool noted = false;
    if (noted) return;
    noted = true;
    std::vector<addr_range> ranges;
    for (loaded_object const & o : loaded_objects()) {
        std::string path;
        bool core = o.main_program;
        if (!core && is_lean_lib(o.name, path)) {
            std::string file = path.substr(path.rfind('/') + 1);
            core = file.compare(0, 13, "libleanshared") == 0 || file.compare(0, 14, "libInit_shared") == 0;
        }
        if (core)
            for (auto const & seg : o.segments) ranges.push_back({ seg.first, seg.second, g_core });
    }
    add_ranges(ranges);
}

// A manifest of `PAPERLEAN_NATIVE_LIBS`.
struct manifest {
    std::string path;           // as listed
    std::string canonical;
    std::string data;
    native_header hdr;
    int32_t lib = -1;           // in `g_libs`, once loaded
    bool needed = false;
    native_module const * modules() const { return reinterpret_cast<native_module const *>(data.data() + hdr.modules_off); }
    native_part const * parts() const { return reinterpret_cast<native_part const *>(data.data() + hdr.parts_off); }
    native_string const * deps() const { return reinterpret_cast<native_string const *>(data.data() + hdr.deps_off); }
    std::string str(native_string s) const { return std::string(data.data() + hdr.strings_off + s.off, s.len); }
    // a recorded path: absolute, or relative to the manifest's directory
    std::string path_of(native_string s) const {
        std::string p = str(s);
        return p.empty() || p[0] == '/' ? p : canonical.substr(0, canonical.rfind('/') + 1) + p;
    }
};

void warn(std::string const & manifest, char const * why) {
    fprintf(stderr, "warning: ignoring native library manifest '%s': %s\n", manifest.c_str(), why);
}

// Reads the manifest at `m.path` if it is a valid manifest of this build; otherwise `why`.
bool read_manifest(manifest & m, char const *& why) {
    if (!canonical_path(m.path, m.canonical)) { why = "cannot be read"; return false; }
    int fd = open(m.canonical.c_str(), O_RDONLY | O_CLOEXEC);
    if (fd < 0) { why = "cannot be read"; return false; }
    struct stat st;
    bool ok = fstat(fd, &st) == 0 && S_ISREG(st.st_mode);
    uint64_t size = ok ? static_cast<uint64_t>(st.st_size) : 0;
    if (ok && (size < sizeof(native_header) || size > g_max_manifest_size)) {
        close(fd);
        why = "not a native library manifest";
        return false;
    }
    try {
        if (ok) m.data.resize(size);
    } catch (std::bad_alloc &) {
        ok = false;
    }
    for (uint64_t done = 0; ok && done < size;) {
        ssize_t r = pread(fd, &m.data[done], size - done, done);
        ok = r > 0;
        if (ok) done += r;
    }
    close(fd);
    if (!ok) { why = "cannot be read"; return false; }
    native_header & hdr = m.hdr;
    memcpy(&hdr, m.data.data(), sizeof(hdr));
    if ((why = check_side_file_header(hdr.common, g_native_kind, sizeof(native_header)))) return false;
    if (hdr.format != g_native_format) { why = "written by a different version"; return false; }
    if (hdr.size != size || native_checksum(hdr, m.data.data() + sizeof(hdr), size - sizeof(hdr)) != hdr.common.checksum) {
        why = "corrupt (checksum mismatch)";
        return false;
    }
    // the tables in order, aligned and within the file, then the strings up to its end
    auto table = [&](uint64_t off, uint64_t n, uint64_t elem, uint64_t next) {
        return off % alignof(uint64_t) == 0 && off <= next && n <= (next - off) / elem;
    };
    if (hdr.modules_off != sizeof(hdr) || hdr.strings_off > size || hdr.strings_size != size - hdr.strings_off ||
        !table(hdr.modules_off, hdr.num_modules, sizeof(native_module), hdr.parts_off) ||
        !table(hdr.parts_off, hdr.num_parts, sizeof(native_part), hdr.deps_off) ||
        !table(hdr.deps_off, hdr.num_deps, sizeof(native_string), hdr.strings_off)) {
        why = "corrupt (bad tables)";
        return false;
    }
    auto str_ok = [&](native_string s) { return s.off <= hdr.strings_size && s.len <= hdr.strings_size - s.off; };
    if (!str_ok(hdr.lib_path) || hdr.lib_path.len == 0) {
        why = "corrupt (bad library path)";
        return false;
    }
    native_module const * mods = m.modules();
    native_part const * parts = m.parts();
    for (uint32_t i = 0; i < hdr.num_modules; i++) {
        native_module const & mm = mods[i];
        if (!str_ok(mm.name) || mm.first_part > hdr.num_parts || mm.num_parts > hdr.num_parts - mm.first_part) {
            why = "corrupt (bad modules)";
            return false;
        }
        for (uint32_t j = 0; j < mm.num_parts; j++) {
            uint32_t kind = parts[mm.first_part + j].kind;
            if (kind >= num_module_file_kinds || (j > 0 && kind <= parts[mm.first_part + j - 1].kind)) {
                why = "corrupt (bad modules)";
                return false;
            }
        }
    }
    for (uint32_t i = 0; i < hdr.num_deps; i++)
        if (!str_ok(m.deps()[i])) { why = "corrupt (bad strings)"; return false; }
    return true;
}

// Whether `files`, of `packed_module_files`, are the files of `mm`.
bool same_files(manifest const & m, native_module const & mm, std::vector<std::pair<uint32_t, file_identity>> const & files) {
    if (files.size() != mm.num_parts) return false;
    for (uint32_t j = 0; j < mm.num_parts; j++) {
        native_part const & p = m.parts()[mm.first_part + j];
        if (files[j].first != p.kind || !(files[j].second == p.id)) return false;
    }
    return true;
}

// Loads the library of `m`, returning its index in `g_libs`, or -1 with a warning.
int32_t load_lib(manifest const & m) {
    std::string lib;
    file_identity id;
    if (!canonical_path(m.path_of(m.hdr.lib_path), lib) || !stat_identity(lib.c_str(), id) || !(id == m.hdr.lib)) {
        warn(m.path, "its library changed");
        return -1;
    }
    std::unique_lock<std::shared_mutex> lock(g_libs_mutex);
    for (size_t k = 0; k < g_libs->size(); k++) {
        if ((*g_libs)[k].path != lib) continue;
        if (!(*g_libs)[k].toolchain && (*g_libs)[k].id == id) return static_cast<int32_t>(k);
        warn(m.path, "its library changed since this process loaded it");
        return -1;
    }
    // A library loaded otherwise may be a different file.
    if (void * other = dlopen(lib.c_str(), RTLD_LAZY | RTLD_NOLOAD)) {
        dlclose(other);
        warn(m.path, "its library is loaded already");
        return -1;
    }
    note_core();
    // Loaded with local symbols first, so that its address ranges are known before the interpreter
    // can find any of its symbols (and promoted to global symbols below).
    std::vector<loaded_object> before = loaded_objects();
    void * handle = dlopen(lib.c_str(), RTLD_LAZY | RTLD_LOCAL);
    if (!handle) {
        char const * err = dlerror();
        warn(m.path, err ? err : "its library cannot be loaded");
        return -1;
    }
    // whether a newly loaded object is the library
#if defined(__linux__)
    link_map * lm = nullptr;
    if (dlinfo(handle, RTLD_DI_LINKMAP, &lm) != 0) lm = nullptr;
    auto is_lib = [&](loaded_object const & o) { return lm && o.base == lm->l_addr && lm->l_name && o.name == lm->l_name; };
#else
    auto is_lib = [&](loaded_object const & o) {
        std::string path;
        return canonical_path(o.name, path) && path == lib;
    };
#endif
    std::vector<addr_range> ranges;
    std::vector<loaded_lib> toolchain;
    bool found = false;
    int32_t k = static_cast<int32_t>(g_libs->size());
    for (loaded_object const & o : loaded_objects()) {
        if (std::any_of(before.begin(), before.end(), [&](loaded_object const & b) {
                return b.base == o.base && b.name == o.name;
            }))
            continue;
        int32_t owner = g_pulled_in;
        std::string path;
        file_identity tid;
        if (is_lib(o)) {
            found = !o.segments.empty();
            owner = k;
        } else if (is_lean_lib(o.name, path) && stat_identity(path.c_str(), tid)) {
            owner = k + 1 + static_cast<int32_t>(toolchain.size());
            toolchain.push_back({ path, tid, true });
        }
        for (auto const & seg : o.segments) ranges.push_back({ seg.first, seg.second, owner });
    }
    file_identity after;
    if (!found || !stat_identity(lib.c_str(), after) || !(after == id)) {
        // none of its code was used
        dlclose(handle);
        warn(m.path, found ? "its library changed" : "its library's address ranges cannot be found");
        return -1;
    }
    g_libs->push_back({ lib, id, false });
    g_libs->insert(g_libs->end(), toolchain.begin(), toolchain.end());
    add_ranges(ranges);
    g_any_loaded = true;
    // now for the interpreter (`lookup_symbol_in_cur_exe`), together with what it pulled in
    if (!dlopen(lib.c_str(), RTLD_LAZY | RTLD_NOLOAD | RTLD_GLOBAL)) {
        warn(m.path, "its library's symbols cannot be made global");
        return -1;
    }
    return k;
}

// The library whose native code the interpreter uses for each imported module of `env` for `opts`,
// whether only for its `meta` declarations, and the module initializers that the import may run
// natively.
bool verify(b_obj_arg env, b_obj_arg opts, char const * list, std::vector<int32_t> & lib_of,
            std::vector<bool> & meta_only, std::unordered_map<std::string, int32_t> & inits) {
    lean_inc(env); lean_inc(opts);
    object_ref info(lean_paperlean_native_import_info(env, opts));
    // `NativeImportInfo`
    object * names = cnstr_get(info.raw(), 0);
    object * runtime_init = cnstr_get(info.raw(), 1);
    object * has_init = cnstr_get(info.raw(), 2);
    object * init_names = cnstr_get(info.raw(), 3);
    object * imports = cnstr_get(info.raw(), 4);
    object * datas = imports_id(env);
    size_t n = array_size(names);
    if (import_timing_enabled()) import_timing_mark("native.info");
    if (array_size(datas) != n) return false;
    auto init_name = [&](size_t idx) { return lean_string_cstr(lean_array_get_core(init_names, idx)); };
    std::unordered_multimap<uint64_t, uint32_t> by_hash;
    for (size_t i = 0; i < n; i++) by_hash.emplace(lean_name_hash(lean_array_get_core(names, i)), static_cast<uint32_t>(i));

    std::vector<manifest> ms;
    std::string s(list);
    for (size_t start = 0; start <= s.size();) {
        size_t end = s.find(':', start);
        if (end == std::string::npos) end = s.size();
        std::string path = s.substr(start, end - start);
        start = end + 1;
        if (path.empty()) continue;
        manifest m;
        m.path = path;
        char const * why = nullptr;
        if (!read_manifest(m, why)) { warn(path, why); continue; }
        ms.push_back(std::move(m));
    }
    // per module, the manifest that verified it, and the initializer flags it records
    std::vector<int32_t> verified_by(n, -1);
    std::vector<uint32_t> init_flags(n, 0);
    std::vector<std::pair<uint32_t, file_identity>> files;
    for (size_t mi = 0; mi < ms.size(); mi++) {
        manifest & m = ms[mi];
        for (uint32_t i = 0; i < m.hdr.num_modules; i++) {
            native_module const & mm = m.modules()[i];
            auto r = by_hash.equal_range(mm.name_hash);
            for (auto it = r.first; it != r.second; ++it) {
                uint32_t idx = it->second;
                if (verified_by[idx] >= 0) continue;
                object * nm = lean_array_get_core(names, idx);
                if (name(nm, true).to_string() != m.str(mm.name)) continue;
                if (packed_module_files(nm, lean_array_get_core(datas, idx), files) && same_files(m, mm, files)) {
                    verified_by[idx] = static_cast<int32_t>(mi);
                    init_flags[idx] = mm.flags;
                    m.needed = true;
                }
            }
        }
    }
    // the libraries they are linked against, listed before them
    std::unordered_map<std::string, size_t> by_path;
    for (size_t mi = 0; mi < ms.size(); mi++) by_path.emplace(ms[mi].canonical, mi);
    std::vector<bool> deps_ok(ms.size(), true);
    for (size_t mi = ms.size(); mi-- > 0;) {
        manifest const & m = ms[mi];
        if (!m.needed) continue;
        for (uint32_t i = 0; i < m.hdr.num_deps; i++) {
            std::string dep;
            auto it = canonical_path(m.path_of(m.deps()[i]), dep) ? by_path.find(dep) : by_path.end();
            if (it == by_path.end() || it->second >= mi) {
                deps_ok[mi] = false;
                continue;
            }
            ms[it->second].needed = true;
        }
    }
    for (size_t mi = 0; mi < ms.size(); mi++) {
        manifest & m = ms[mi];
        if (!m.needed) continue;
        bool ok = deps_ok[mi];
        for (uint32_t i = 0; ok && i < m.hdr.num_deps; i++) {
            std::string dep;
            ok = canonical_path(m.path_of(m.deps()[i]), dep) && ms[by_path[dep]].lib >= 0;
        }
        if (!ok) { warn(m.path, "a library it is linked against is not used"); continue; }
        m.lib = load_lib(m);
    }
    if (import_timing_enabled()) import_timing_mark("native.load");

    // Whether the native code of each module may be used, for all of it or for its `meta`
    // declarations only. A module's initializer, and with it its code, must resolve into its
    // verified library (or Lean's own code), and the initializers that its native initializers run
    // must be those that `runInitAttrForMod` runs, in the same order (`EmitC.lean`, `emitInitFn`):
    // - All of a module's native code is used if its runtime initializer runs, and all of the code
    //   of its direct imports is used (or Lean's own, which is initialized at startup); its runtime
    //   initializer runs those of its regular imports, its compile-time initializer those of its
    //   `meta import`s.
    // - Only its `meta` code is used if only its compile-time initializer runs, its runtime
    //   initializer initializes nothing (`meta` code can use declarations that the compiler
    //   generates, which belong to both phases), all of the code of its `meta import`s is used,
    //   and the `meta` code of its other direct imports (`meta` code may use only that, which the
    //   module system ensures).
    // - The runtime initializers that run early this way, before their module's turn, must run no
    //   `[init]` declarations: they are those of modules that come after it in the import order (a
    //   flag bump of the import can do that).
    // - If its compile-time initializer initializes declarations, which can use the `meta` code of
    //   any module that it imports directly or indirectly, those of these whose compile-time
    //   initializers initialize declarations must come before it, so that these have run.
    // - A regular import that is not imported (a private import of a module imported for run time
    //   only) is called neither by its `meta` code (the module system lets `meta` code reachable
    //   from other modules use only public imports) nor by its compile-time initializer, if that
    //   initializes nothing.
    // By depth-first search; core modules import only core modules.
    std::vector<int32_t> owner(n, g_not_found - 1);
    auto owner_of_module = [&](size_t x) {
        if (owner[x] < g_not_found) {
            void * a = dlsym(RTLD_DEFAULT, init_name(x));
            owner[x] = a ? owner_of(reinterpret_cast<uintptr_t>(a)) : g_not_found;
        }
        return owner[x];
    };
    std::vector<bool> toolchain;
    {
        std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
        for (loaded_lib const & l : *g_libs) toolchain.push_back(l.toolchain);
    }
    lib_of.assign(n, -1);
    meta_only.assign(n, false);
    // 0: not visited, 1: being visited, 2: visited
    std::vector<uint8_t> state(n, 0);
    std::vector<bool> full_ok(n, false), meta_ok(n, false);
    // the greatest index of a module with `[init]` declarations that the module's runtime
    // initializer runs, the module included, and of a module whose compile-time initializer
    // initializes declarations, which it imports directly or indirectly (-1 if none)
    std::vector<int64_t> last_init(n, -1), last_meta_init(n, -1);
    std::vector<bool> meta_inits_of(n, true);
    std::vector<std::pair<size_t, size_t>> stack;
    size_t used = 0, used_meta = 0, not_runtime = 0, not_imports = 0, not_order = 0;
    std::vector<bool> lib_used(ms.size(), false);
    for (size_t root = 0; root < n; root++) {
        if (state[root]) continue;
        state[root] = 1;
        stack.push_back({ root, 0 });
        while (!stack.empty()) {
            size_t x = stack.back().first;
            object * imps = lean_array_get_core(imports, x);
            int32_t own = owner_of_module(x);
            if (own != g_core && stack.back().second < array_size(imps)) {
                size_t j = lean_unbox(lean_array_get_core(imps, stack.back().second++)) / 2;
                if (j < n && state[j] == 0) {
                    state[j] = 1;
                    stack.push_back({ j, 0 });
                }
                continue;
            }
            stack.pop_back();
            state[x] = 2;
            if (own == g_core) {
                full_ok[x] = meta_ok[x] = true;
                continue;
            }
            int64_t self = static_cast<int64_t>(x);
            bool verified = own >= 0 && (toolchain[own] || (verified_by[x] >= 0 && ms[verified_by[x]].lib == own));
            bool code_ok = own == g_elsewhere || verified;
            // the module's initializer flags, as the manifest records them, or what they can be
            uint32_t flags = verified_by[x] >= 0 ? init_flags[x] : 0;
            bool known = flags & native_init_known;
            bool runs_init = known ? (flags & native_runtime_init_runs) : lean_unbox(lean_array_get_core(has_init, x));
            bool meta_inits = known ? (flags & native_meta_init_initializes) : true;
            bool runtime_inits = known ? (flags & native_runtime_init_initializes) : true;
            meta_inits_of[x] = meta_inits;
            bool full_imports = true, meta_imports = true, early_ok = true;
            int64_t last = -1, last_meta = -1;
            for (size_t i = 0; i < array_size(imps); i++) {
                size_t v = lean_unbox(lean_array_get_core(imps, i));
                size_t j = v / 2;
                if (j >= n) {
                    full_imports = false;
                    if (v % 2 || meta_inits) meta_imports = false;
                    continue;
                }
                if (owner[j] == g_core) continue;
                full_imports = full_imports && full_ok[j];
                meta_imports = meta_imports && (v % 2 ? full_ok[j] : meta_ok[j]);
                // its initializers run the import's runtime initializer
                if (v % 2 || lean_unbox(lean_array_get_core(runtime_init, x))) early_ok = early_ok && last_init[j] < self;
                if (v % 2 == 0) last = std::max(last, last_init[j]);
                last_meta = std::max(last_meta, std::max(meta_inits_of[j] ? static_cast<int64_t>(j) : -1, last_meta_init[j]));
            }
            bool runtime = lean_unbox(lean_array_get_core(runtime_init, x));
            bool order = early_ok && (!meta_inits || last_meta < self);
            full_ok[x] = code_ok && runtime && full_imports && order;
            meta_ok[x] = full_ok[x] || (code_ok && !runtime && !runtime_inits && meta_imports && order);
            last_init[x] = runs_init ? std::max(last, self) : last;
            last_meta_init[x] = last_meta;
            if (own >= 0 && verified_by[x] >= 0 && !meta_ok[x]) {
                // for `PAPERLEAN_IMPORT_TIMING`: why verified modules are not used
                if (!(runtime ? full_imports : meta_imports)) not_imports++;
                else if (!order) not_order++;
                else not_runtime++;
            }
            if (own < 0 || !meta_ok[x]) continue;
            lib_of[x] = own;
            meta_only[x] = !full_ok[x];
            // as `mkModuleInitializationPrefix` names them
            for (char const * prefix : { "", "runtime_", "meta_" })
                if (full_ok[x] || prefix[0] == 'm') inits.emplace(std::string(prefix) + init_name(x), own);
            if (!toolchain[own]) {
                (full_ok[x] ? used : used_meta)++;
                lib_used[verified_by[x]] = true;
            }
        }
    }
    if (import_timing_enabled()) {
        size_t verified = std::count_if(verified_by.begin(), verified_by.end(), [](int32_t mi) { return mi >= 0; });
        std::string mark = "native libs=" + std::to_string(std::count(lib_used.begin(), lib_used.end(), true)) +
            " modules=" + std::to_string(used) + " meta=" + std::to_string(used_meta) +
            " verified=" + std::to_string(verified) + " importsNotUsed=" + std::to_string(not_imports) +
            " initOrder=" + std::to_string(not_order) + " other=" + std::to_string(not_runtime);
        import_timing_mark(mark.c_str());
    }
    return used + used_meta > 0;
}
#endif
}

void * filter_native_symbol(b_obj_arg env, b_obj_arg fn, void * addr) {
#ifdef PAPERLEAN_NATIVE_LIBS
    if (!addr || !g_any_loaded.load(std::memory_order_acquire)) return addr;
    int32_t owner = owner_of(reinterpret_cast<uintptr_t>(addr));
    if (owner == g_pulled_in) return nullptr;
    // Lean's own code, or a library loaded otherwise, which Lean uses as well
    if (owner < 0) return addr;
    uncounted_heartbeats uncounted;
    lean_object * h = imports_id(env);
    native_modules const * mods = nullptr;
    {
        std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
        auto it = g_native_modules->find(h);
        if (it != g_native_modules->end()) mods = &it->second;
    }
    if (!mods) return nullptr;
    lean_inc(env); lean_inc(fn);
    uint32 idx = lean_paperlean_const_module_idx(env, fn);
    if (idx == 0 || idx - 1 >= mods->lib_of.size() || mods->lib_of[idx - 1] != owner) return nullptr;
    if (mods->meta_only[idx - 1]) {
        lean_inc(env); lean_inc(fn);
        if (!lean_paperlean_is_meta_const(env, fn)) return nullptr;
    }
    return addr;
#else
    (void)env; (void)fn;
    return addr;
#endif
}

void * filter_native_initializer(char const * sym, void * addr) {
#ifdef PAPERLEAN_NATIVE_LIBS
    if (!addr || !g_any_loaded.load(std::memory_order_acquire)) return addr;
    int32_t owner = owner_of(reinterpret_cast<uintptr_t>(addr));
    if (owner != g_pulled_in && owner < 0) return addr;
    if (owner == g_pulled_in || !g_finalizing || g_finalizing->empty() || !g_finalizing->back().inits) return nullptr;
    auto const & inits = *g_finalizing->back().inits;
    auto it = inits.find(sym);
    return it != inits.end() && it->second == owner ? addr : nullptr;
#else
    (void)sym;
    return addr;
#endif
}

/* nativeLibsAvailableCore : Unit → Bool */
extern "C" LEAN_EXPORT uint8 lean_paperlean_native_libs_available(obj_arg) {
#ifdef PAPERLEAN_NATIVE_LIBS
    return 1;
#else
    return 0;
#endif
}

/* loadNativeLibs (env : @& Environment) (opts : @& Options) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_load_native_libs(b_obj_arg env, b_obj_arg opts) {
#ifdef PAPERLEAN_NATIVE_LIBS
    char const * list = getenv("PAPERLEAN_NATIVE_LIBS");
    if (!list || !*list || lean_heartbeats_mode()) return lean_box(0);
    // PaperLean's work, not counted as heartbeats
    uncounted_heartbeats uncounted;
    lean_object * h = imports_id(env);
    if (!g_finalizing) g_finalizing = new std::vector<native_inits>();
    g_finalizing->push_back({ h, nullptr });
    // only for imports that are never freed, which their module data identifies for good
    if (lean_is_scalar(h) || !lean_is_persistent(h)) return lean_box(0);
    try {
        native_modules mods;
        auto * inits = new std::unordered_map<std::string, int32_t>();
        if (verify(env, opts, list, mods.lib_of, mods.meta_only, *inits)) {
            std::unique_lock<std::shared_mutex> lock(g_libs_mutex);
            g_native_modules->emplace(h, std::move(mods));
            g_finalizing->back().inits = inits;
        } else {
            delete inits;
        }
    } catch (std::exception & ex) {
        fprintf(stderr, "warning: not using native libraries: %s\n", ex.what());
    }
#else
    (void)env; (void)opts;
#endif
    return lean_box(0);
}

/* endNativeInit (env : @& Environment) : BaseIO Unit -- when `finalizePersistentExtensions` ends */
extern "C" LEAN_EXPORT obj_res lean_paperlean_end_native_init(b_obj_arg env) {
    if (!g_finalizing || g_finalizing->empty()) return lean_box(0);
    uncounted_heartbeats uncounted;
    if (g_finalizing->back().imports == imports_id(env)) {
        // the import's own initializers have run; later ones are interpreted
        delete g_finalizing->back().inits;
        g_finalizing->pop_back();
    }
    return lean_box(0);
}

#ifdef PAPERLEAN_NATIVE_LIBS
namespace {
// The flags `native_runtime_init_runs`, `native_meta_init_initializes` and
// `native_runtime_init_initializes` of the module whose `.c` file (`EmitC.lean`) is `path`: a
// statement of an initializer that is not part of its frame, a call of an import's initializer or a
// builtin initialization (which `runInitAttrForMod` does not run) runs an `[init]` declaration
// (`res = ...`) or initializes a declaration. A file without initializers for the phases has only
// the one for all phases.
bool c_init_flags(char const * path, uint32_t & flags) {
    FILE * f = fopen(path, "rb");
    if (!f) return false;
    std::string c;
    char buf[1 << 16];
    for (size_t r; (r = fread(buf, 1, sizeof(buf), f)) > 0;) c.append(buf, r);
    fclose(f);
    // what the body of the initializer named `<prefix>initialize_...` does
    auto scan = [&](char const * prefix, bool & runs, bool & initializes) {
        std::string head = std::string("\nLEAN_EXPORT lean_object* ") + prefix + "initialize_";
        size_t at = c.find(head);
        if (at == std::string::npos) return false;
        size_t line_end = c.find('\n', at + 1);
        if (line_end == std::string::npos || line_end < 19 || c.compare(line_end - 19, 20, "(uint8_t builtin) {\n") != 0) return false;
        size_t end = c.find("\n}\n", line_end);
        if (end == std::string::npos) return false;
        int in_builtin = 0;
        for (size_t p = line_end + 1; p < end;) {
            size_t q = c.find('\n', p);
            if (q == std::string::npos || q > end) q = end;
            std::string_view l(c.data() + p, q - p);
            p = q + 1;
            auto starts = [&](std::string_view x) { return l.substr(0, x.size()) == x; };
            auto ends = [&](std::string_view x) { return l.size() >= x.size() && l.substr(l.size() - x.size()) == x; };
            if (l == "if (builtin) {") { in_builtin++; continue; }
            if (in_builtin) { if (l == "}") in_builtin--; continue; }
            if (l == "lean_object * res;" || starts("if (_G_") || starts("_G_") || l == "lean_initialize();" ||
                l == "lean_initialize_runtime_module();" || l == "if (lean_io_result_is_error(res)) return res;" ||
                l == "lean_dec_ref(res);" || starts("return "))
                continue;
            if (starts("res = ") && ends("(builtin);") && l.find("initialize_") != std::string_view::npos) continue;
            initializes = true;
            if (starts("res = ")) runs = true;
        }
        return !in_builtin;
    };
    bool runtime_runs = false, runtime_inits = false, meta_runs = false, meta_inits = false;
    if (scan("runtime_", runtime_runs, runtime_inits)) {
        if (!scan("meta_", meta_runs, meta_inits)) return false;
    } else if (!scan("", runtime_runs, runtime_inits)) {
        return false;
    } else {
        meta_inits = runtime_inits;
    }
    flags = native_init_known | (runtime_runs ? native_runtime_init_runs : 0) |
        (meta_inits ? native_meta_init_initializes : 0) | (runtime_inits ? native_runtime_init_initializes : 0);
    return true;
}
}
#endif

/* writeNativeManifestCore (out lib : @& String) (deps : @& Array String)
     (modules : @& Array (Name × String × Array String)) : IO Unit
   Writes the manifest of the native library `lib` of `modules`, each with the `.c` file compiled into
   `lib` and the paths of its files by kind (`module_file_kind`, empty if it has none), linked
   against the libraries of the manifests `deps`. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_write_native_manifest(b_obj_arg oout, b_obj_arg olib, b_obj_arg odeps,
                                                                    b_obj_arg omodules) {
#ifdef PAPERLEAN_NATIVE_LIBS
    std::string strings;
    auto add = [&](std::string const & x) {
        native_string r { strings.size(), x.size() };
        strings += x;
        return r;
    };
    auto fail = [](std::string const & what) {
        return io_result_mk_error((sstream() << "writeNativeManifest: " << what).str().c_str());
    };
    native_header hdr;
    memset(&hdr, 0, sizeof(hdr));
    init_side_file_header(hdr.common, g_native_kind, sizeof(native_header));
    hdr.format = g_native_format;
    std::string lib, out_dir;
    if (!canonical_path(lean_string_cstr(olib), lib) || !stat_identity(lib.c_str(), hdr.lib))
        return fail(std::string("cannot read ") + lean_string_cstr(olib));
    // a file next to the manifest is recorded by its name, so that the two can move together
    std::string out_path = lean_string_cstr(oout);
    canonical_path(out_path.find('/') == std::string::npos ? "." : out_path.substr(0, out_path.rfind('/')), out_dir);
    auto recorded = [&](std::string const & p) {
        return !out_dir.empty() && dir_of(p) == out_dir ? p.substr(p.rfind('/') + 1) : p;
    };
    hdr.lib_path = add(recorded(lib));
    std::vector<native_module> mods;
    std::vector<native_part> parts;
    for (size_t i = 0; i < lean_array_size(omodules); i++) {
        object * p = lean_array_get_core(omodules, i);
        object * n = lean_ctor_get(p, 0);
        char const * cfile = lean_string_cstr(lean_ctor_get(lean_ctor_get(p, 1), 0));
        object * paths = lean_ctor_get(lean_ctor_get(p, 1), 1);
        native_module m;
        memset(&m, 0, sizeof(m));
        if (!c_init_flags(cfile, m.flags)) return fail(std::string("cannot read the initializers of ") + cfile);
        // as the loader compares the imported modules' names
        m.name = add(name(n, true).to_string());
        m.name_hash = lean_name_hash(n);
        m.first_part = static_cast<uint32_t>(parts.size());
        if (lean_array_size(paths) != num_module_file_kinds) return fail("expected a path per kind of file");
        for (uint32_t kind = 0; kind < num_module_file_kinds; kind++) {
            char const * path = lean_string_cstr(lean_array_get_core(paths, kind));
            if (!*path) continue;
            native_part part;
            memset(&part, 0, sizeof(part));
            part.kind = kind;
            if (!stat_identity(path, part.id)) return fail(std::string("cannot read ") + path);
            parts.push_back(part);
        }
        m.num_parts = static_cast<uint32_t>(parts.size()) - m.first_part;
        mods.push_back(m);
    }
    std::vector<native_string> deps;
    for (size_t i = 0; i < lean_array_size(odeps); i++) {
        std::string dep;
        if (!canonical_path(lean_string_cstr(lean_array_get_core(odeps, i)), dep))
            return fail(std::string("cannot read ") + lean_string_cstr(lean_array_get_core(odeps, i)));
        deps.push_back(add(recorded(dep)));
    }
    hdr.num_modules = static_cast<uint32_t>(mods.size());
    hdr.num_parts = static_cast<uint32_t>(parts.size());
    hdr.num_deps = static_cast<uint32_t>(deps.size());
    hdr.modules_off = sizeof(hdr);
    hdr.parts_off = hdr.modules_off + mods.size() * sizeof(native_module);
    hdr.deps_off = hdr.parts_off + parts.size() * sizeof(native_part);
    hdr.strings_off = hdr.deps_off + deps.size() * sizeof(native_string);
    hdr.strings_size = strings.size();
    hdr.size = hdr.strings_off + strings.size();
    std::string body;
    body.append(reinterpret_cast<char const *>(mods.data()), mods.size() * sizeof(native_module));
    body.append(reinterpret_cast<char const *>(parts.data()), parts.size() * sizeof(native_part));
    body.append(reinterpret_cast<char const *>(deps.data()), deps.size() * sizeof(native_string));
    body += strings;
    hdr.common.checksum = native_checksum(hdr, body.data(), body.size());
    std::string out = lean_string_cstr(oout);
    std::string tmp = out + ".tmp";
    FILE * f = fopen(tmp.c_str(), "wb");
    if (!f) return fail("cannot write " + tmp);
    bool ok = fwrite(&hdr, 1, sizeof(hdr), f) == sizeof(hdr) && fwrite(body.data(), 1, body.size(), f) == body.size();
    ok = fclose(f) == 0 && ok;
    if (!ok || rename(tmp.c_str(), out.c_str()) != 0) return fail("cannot write " + out);
    return io_result_mk_ok(lean_box(0));
#else
    (void)oout; (void)olib; (void)odeps; (void)omodules;
    return io_result_mk_error("writeNativeManifest: native libraries are supported only on Linux and macOS");
#endif
}
}
