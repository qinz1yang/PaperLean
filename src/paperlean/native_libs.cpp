/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <algorithm>
#include <atomic>
#include <cctype>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <mutex>
#include <new>
#include <shared_mutex>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
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
#include "paperlean/side_file_output.h"
#include "paperlean/native_libs.h"

/*
Native libraries of packages: shared libraries compiled from the `.c` files of a package's modules,
prepared locally, each with a manifest (`.paperlean`, kind `native-lib`) that records the library's
file identity and, for every module compiled into it, the content hashes of the module's files
(`.olean`, `.olean.server`, `.olean.private`, `.ir.sig`, `.ir`) the `.c` file was generated with, so
that a library serves every workspace whose packs hold these files (`Lake.PaperLean.Cache`).
`PAPERLEAN_NATIVE_LIBS` is a `:`-separated list of manifests, dependencies first (on Linux and
macOS).

When `finalizePersistentExtensions` starts, before the interpreter first runs for the environment,
`lean_paperlean_load_native_libs` decides per imported module whether the interpreter uses the
native code of a library for it, as with `--load-dynlib`, or interprets it as without native
libraries. It uses a library's code for a module only if
- an import got the module's data from an olean pack (the data are the root of a packed part of
  the module) and the files the pack holds for the module, unchanged since packing (or binding), are
  exactly those of the manifest;
- the module's initializer resolves into that library, so that its symbols are the library's;
- its native code does nothing that interpreting it would not (`native_differs`): it declares no
  `@[extern]` functions (whose native code would call whatever has their symbols, while the
  interpreter calls none of a package's), has no `builtin_initialize` declarations (which only native
  initializers run), and evaluating its nullary constants does nothing that depends on when or how
  often it happens (`Lean.PaperLean.evalImpuritiesMain`): native code evaluates them once per process,
  the interpreter when they are first used, again in each of its runs;
- the initializers that native code runs are those that the interpreter would run, in the same
  order: `runInitAttrForMod` runs the module's runtime initializer (which initializes its
  non-`meta` declarations; then all of its code is used, if it has no `[init]` declarations of one
  of the phases, which its initializers would run in another order) or only its compile-time
  initializer (which initializes its `meta` declarations; then only these are used); the native
  initializers of a module run the runtime initializers of its direct imports (only of its `meta
  import`s for the compile-time initializer), so these must use all of their code, and come before
  it in the import order if they have `[init]` declarations;
- the same holds for the code that it calls: that of its direct imports (only their `meta`
  declarations through regular imports of a module of which only `meta` code is used, which the
  module system ensures, and which must then come before it), unless that is Lean's own code (Lean's
  own libraries, including those that they depend on, such as `libLake_shared`, or a library loaded
  otherwise, which Lean would use as well, unless one of these libraries has the module too: its code
  for the module's importers would use its own copy).
The interpreter's lookups (`library/ir_interpreter.cpp`) then get an address in these libraries only
for a declaration of such a module, of the library verified for it, and a module initializer only for
such a module of the import being finalized on the thread; other addresses in these libraries, and
in libraries they pulled in that are not Lean's own, are filtered out. A module without native code
is interpreted, with the same results. A module whose native initializers ran runs none of its
initializers in later imports of the process, as the interpreter runs those of a module once, and
keeps its native code there if it has the same files, as code loaded with `--load-dynlib` does
(otherwise only the values of its `[init]` declarations, which the interpreter keeps by name).

Format: `native_header`, then `native_module`s, `native_part`s, the manifests of the libraries it
is linked against (`native_string`s), and the strings; the checksum covers everything after the
header.
*/

namespace lean {
// These are the spellings and ABIs of Init.Data.Float.{Float,Float32}. EmitC writes their
// declarations into importing C files, even though the extern attribute belongs to Init.
// A retained object binds these calls directly to this toolchain, never to a package export.
struct native_math_op {
    std::string_view name, prototype;
    unsigned arity;
};
constexpr native_math_op g_math_ops[] = {
    {"ceil",   "double ceil(double);",        1},
    {"floor",  "double floor(double);",       1},
    {"floorf", "float floorf(float);",        1},
    {"pow",    "double pow(double, double);", 2},
    {"sqrt",   "double sqrt(double);",        1}
};
static native_math_op const * native_math(std::string_view name) {
    for (auto const & op : g_math_ops) if (op.name == name) return &op;
    return nullptr;
}
constexpr std::string_view g_math_prefix = "lean_paperlean_stdmath_";
extern "C" LEAN_EXPORT double lean_paperlean_stdmath_ceil(double x) { return std::ceil(x); }
extern "C" LEAN_EXPORT double lean_paperlean_stdmath_floor(double x) { return std::floor(x); }
extern "C" LEAN_EXPORT float lean_paperlean_stdmath_floorf(float x) { return std::floor(x); }
extern "C" LEAN_EXPORT double lean_paperlean_stdmath_pow(double x, double y) { return std::pow(x, y); }
extern "C" LEAN_EXPORT double lean_paperlean_stdmath_sqrt(double x) { return std::sqrt(x); }
// `Lean.PaperLean.Import`; the arguments are owned
extern "C" obj_res lean_paperlean_env_imports_id(obj_arg env);
extern "C" uint32 lean_paperlean_const_module_idx(obj_arg env, obj_arg n);
extern "C" obj_res lean_paperlean_const_module_name(obj_arg env, obj_arg n);
extern "C" uint8 lean_paperlean_is_meta_const(obj_arg env, obj_arg n);
extern "C" uint8 lean_paperlean_imported_has_init(obj_arg env, obj_arg n, uint32 idx);
extern "C" obj_res lean_paperlean_native_import_info(obj_arg env, obj_arg opts);
extern "C" obj_res lean_paperlean_import_packages(obj_arg env);
extern "C" obj_res lean_paperlean_module_init_symbol(obj_arg env, obj_arg idx);
extern "C" LEAN_EXPORT obj_res lean_paperlean_load_native_libs(b_obj_arg env, b_obj_arg opts);

namespace {
constexpr char g_native_kind[] = "native-lib";
constexpr uint32_t g_native_format = 6;
constexpr uint64_t g_max_manifest_size = uint64_t(1) << 30;
// The most modules of each kind that an import tells the summary of a build about.
constexpr size_t g_max_by_import = 100;
// What an import tells the summary of a build (`Lake.PaperLean.ReuseSummary.Fallbacks`) about a module
// that runs in the interpreter in it, and why: `always` if that holds of each import of the module that
// no plugin loads it for, `here` if another import may use its code. Only the import knows, so that all
// of them are told of, also those that `paperlean prepare` found. `rejected` and `left out` are for files
// of the prepared data, so that what that holds of them holds; nothing else that it found is sure to.
constexpr char g_no_library[] = "always\tno prepared native library has it";
constexpr char g_files_changed[] = "always\tits files are not those that `paperlean prepare` read";
constexpr char g_rejected[] = "always\trejected";
constexpr char g_left_out[] = "always\tleft out";
constexpr char g_imports[] = "always\timports";
constexpr char g_imports_here[] = "here\timports";
constexpr char g_imports_plugin[] = "here\tit imports a module whose native code a plugin loaded, so its library's code is not used";
constexpr char g_not_usable[] = "here\tits library's code cannot be used in this import";
constexpr char g_import_not_used[] = "here\tthis import does not use all of what it imports";
constexpr char g_order[] = "here\tits initializers would run in another order";
constexpr char g_mixed[] = "here\tit has `[init]` declarations of both phases";
constexpr char g_no_runtime_init[] = "here\tan import does not run its runtime initializer, which its `meta` code needs";
// What it tells about a module whose native code something else loaded, whatever `paperlean prepare` said.
constexpr char g_loaded[] = "loaded";

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
    uint32_t flags, unused;     // `native_*`
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
// Its native code does something that interpreting it would not (see above), by the entries of its
// `.olean` parts (an import may have only its IR, which tells neither).
constexpr uint32_t native_differs = 16;
// Its compile-time initializer runs `[init]` declarations.
constexpr uint32_t native_meta_init_runs = 32;
// The code that its compile-time initializer runs is its own or Lean's (by its `.c` file), so that
// it does not need the compile-time initializers of other modules to have run.
constexpr uint32_t native_meta_init_local = 64;
// Its `meta` code (what its compile-time initializer and its `meta` declarations run) uses none of
// the declarations that its runtime initializer initializes, and enters the code of other modules
// only at their `meta` declarations' symbols (`native_meta_code_enters_meta`).
constexpr uint32_t native_meta_code_safe = 128;
// Its `meta` code enters the code of other modules, except Lean's own, only at the symbols of their
// declarations marked `meta` (`ModuleNativeData.metaSymbols`), whose own `meta` code they are.
constexpr uint32_t native_meta_code_enters_meta = 256;
// A file of a module; the files of a module are in increasing order of kind.
struct native_part {
    uint32_t kind, unused;      // `module_file_kind`
    content_hash hash;          // of its contents
};

uint64_t native_checksum(native_header hdr, char const * body, size_t size) {
    hdr.common.checksum = 0;
    return side_file_checksum(body, size, side_file_checksum(&hdr, sizeof(hdr)));
}

// A module of these libraries whose initializers an import may run.
struct native_init {
    int32_t lib;
    std::string module;
    std::string init_name;      // its initializer for all phases (`mkModuleInitializationFunctionName`)
    bool meta_only;             // only the module's `meta` code is used
    std::vector<std::pair<uint32_t, content_hash>> files;  // `packed_module_files`
};
// The imports of the environment being finalized on this thread (`lean_paperlean_env_imports_id`),
// the module initializers of these libraries that its finalization may run, if it uses any, and the
// module initializers that `verify` found in Lean's own code or in these libraries, which
// `runInitAttrForMod` looks up again (an image loaded later comes later in the search order) while
// `g_libs_generation` is `generation`.
struct native_inits {
    lean_object * imports;
    std::unordered_map<std::string, std::shared_ptr<native_init const>> * inits;
    std::unordered_map<std::string, void *> * found;
    uint64_t generation;
    uint64_t serial;    // of this finalization, in the process
};
LEAN_THREAD_PTR(std::vector<native_inits>, g_finalizing);

std::atomic<uint64_t> g_finalizations{0};

// The modules whose native initializers ran in this process, with the library, `meta_only` and
// files of that import and the finalization that ran them, and the names of their initializers.
// Later imports run none of their initializers, whichever phase they ask for, as Lean's interpreter
// runs those of a module at most once (`runInitAttrForMod`): a module of the same files keeps its
// native code, as code loaded with `--load-dynlib` does, one of other files keeps the values of its
// `[init]` declarations, which the interpreter keeps by name, and its other code is interpreted.
// (`g_libs_mutex`)
struct initialized_module {
    int32_t lib;
    bool meta_only;
    std::vector<std::pair<uint32_t, content_hash>> files;
    uint64_t serial;
};
std::unordered_map<std::string, initialized_module> * g_initialized_modules =
    new std::unordered_map<std::string, initialized_module>();
std::unordered_map<std::string, std::string> * g_initialized_inits = new std::unordered_map<std::string, std::string>();

// What a module's initializer does when it ran already.
lean_object * already_initialized(uint8_t) { return lean_io_result_mk_ok(lean_box(0)); }

// The prefixes of a module's initializers (`mkModuleInitializationPrefix`).
constexpr char const * g_init_prefixes[] = { "", "runtime_", "meta_" };

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
// changed whenever a library's symbols become visible to `dlsym(RTLD_DEFAULT, ...)`
std::atomic<uint64_t> g_libs_generation{0};
std::vector<addr_range> * g_ranges = new std::vector<addr_range>();   // sorted, disjoint
std::atomic<bool> g_any_loaded{false};
// Per import (`lean_paperlean_env_imports_id`, persistent, so never freed) that loaded these
// libraries, per module index, the library whose native code is used for the module, or -1, and
// whether only for its `meta` declarations, and the library of these that has the module's
// initializer, or -1 (also if it is one of Lean's own).
struct native_modules {
    std::vector<int32_t> lib_of;
    std::vector<bool> meta_only;
    std::vector<int32_t> init_lib;
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

// Whether the file `path` of Lean's own libraries is `libInit_shared` or one of `libleanshared*`.
bool is_core_lib(std::string const & path) {
    std::string file = path.substr(path.rfind('/') + 1);
    return file.compare(0, 13, "libleanshared") == 0 || file.compare(0, 14, "libInit_shared") == 0;
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
        if (!core && is_lean_lib(o.name, path)) core = is_core_lib(path);
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
    side_file_warning("warning: ignoring native library manifest '%s': %s\n", manifest.c_str(), why);
}

// Reads the manifest at `m.path` if it is a valid manifest of this build; otherwise `why`.
bool read_manifest(manifest & m, char const *& why) {
    if (!canonical_path(m.path, m.canonical)) { why = "cannot be read"; return false; }
    int fd = open(m.canonical.c_str(), O_RDONLY | O_CLOEXEC | O_NONBLOCK);
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
bool same_files(manifest const & m, native_module const & mm, std::vector<std::pair<uint32_t, content_hash>> const & files) {
    if (files.size() != mm.num_parts) return false;
    for (uint32_t j = 0; j < mm.num_parts; j++) {
        native_part const & p = m.parts()[mm.first_part + j];
        if (files[j].first != p.kind || !(files[j].second == p.hash)) return false;
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
    // can find any of its symbols (and promoted to global symbols below). All of its symbols are
    // bound now: one that nothing defines (`prepare` leaves out the modules that refer to one, but a
    // library may have been built differently) must fail here, where Lean goes on without the
    // library, not at its first call, where the process dies.
    std::vector<loaded_object> before = loaded_objects();
    void * handle = dlopen(lib.c_str(), RTLD_NOW | RTLD_LOCAL);
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
    g_libs_generation++;
    if (!dlopen(lib.c_str(), RTLD_NOW | RTLD_NOLOAD | RTLD_GLOBAL)) {
        warn(m.path, "its library's symbols cannot be made global");
        return -1;
    }
    return k;
}

typedef std::vector<std::pair<std::string, char const *>> by_import_notes;

// Whether the module `x` of `packages` (`NativeImportInfo`) belongs to a dependency of what a
// `paperlean` command builds: another package than the one that it names (`built`,
// `PAPERLEAN_ROOT_PACKAGE`), whose own modules no library has.
bool of_dependency(char const * built, object * packages, size_t x) {
    object * pkg = lean_array_get_core(packages, x);
    return built && lean_string_size(pkg) > 1 && strcmp(lean_string_cstr(pkg), built) != 0;
}

void note_by_import(by_import_notes & notes, object * names, size_t x, char const * why) {
    if (notes.size() <= g_max_by_import) notes.push_back({ name(lean_array_get_core(names, x), true).to_string(), why });
}

// What an import tells about its module `x`, of `names` and `datas`, that no manifest lists. A module
// from a pack that did not change since has the files of that pack, of which alone the prepared data
// holds what `paperlean prepare` found (`Lake.PaperLean.keptFindings`).
char const * unlisted_why(object * names, object * datas, size_t x) {
    std::vector<std::pair<uint32_t, content_hash>> files;
    bool same = packed_module_files(lean_array_get_core(names, x), lean_array_get_core(datas, x), files);
    return same ? g_left_out : g_no_library;
}

// Gives the summary of a build (`Lake.PaperLean.ReuseSummary`) what this import did with its modules.
void write_by_import(by_import_notes const & notes, by_import_notes const & loaded) {
    char const * stats = notes.empty() && loaded.empty() ? nullptr : getenv("PAPERLEAN_NATIVE_STATS");
    if (!stats) return;
    // (the statistics stay small for all of the `lean` processes of a build)
    std::string text;
    for (by_import_notes const * ns : { &notes, &loaded })
        for (size_t i = 0; i < ns->size() && i < g_max_by_import; i++)
            text += "native\t" + (*ns)[i].first + "\t" + (*ns)[i].second + "\n";
    if (notes.size() > g_max_by_import || loaded.size() > g_max_by_import) text += "native\t*\tmore\n";
    FILE * f = fopen(stats, "a");
    // (at once, as these processes write at the same time)
    bool written = f && setvbuf(f, nullptr, _IONBF, 0) == 0 && fwrite(text.data(), 1, text.size(), f) == text.size();
    if (f) fclose(f);
    if (!written) side_file_warning("warning: the summary of this build lacks an import: '%s' cannot be written\n", stats);
}

// The library whose native code the interpreter uses for each imported module of `env` for `opts`,
// whether only for its `meta` declarations, and the module initializers that the import may run
// natively.
bool verify(b_obj_arg env, b_obj_arg opts, char const * list, native_modules & mods,
            std::unordered_map<std::string, std::shared_ptr<native_init const>> & inits,
            std::unordered_map<std::string, void *> & found, uint64_t & generation) {
    std::vector<int32_t> & lib_of = mods.lib_of;
    std::vector<bool> & meta_only = mods.meta_only;
    lean_inc(env); lean_inc(opts);
    object_ref info(lean_paperlean_native_import_info(env, opts));
    // `NativeImportInfo`
    object * names = cnstr_get(info.raw(), 0);
    object * runtime_init = cnstr_get(info.raw(), 1);
    object * has_init = cnstr_get(info.raw(), 2);
    object * init_names = cnstr_get(info.raw(), 3);
    object * imports = cnstr_get(info.raw(), 4);
    object * env_differs = cnstr_get(info.raw(), 5);
    object * packages = cnstr_get(info.raw(), 6);
    object * mixed_inits = cnstr_get(info.raw(), 7);
    // the initializer that `runInitAttrForMod` looks up last for a module of a `module`, the only one
    // otherwise (`mkModuleInitializationPrefix`)
    char const * init_prefix = lean_ctor_get_uint8(info.raw(), sizeof(void *) * 8) ? "meta_" : "";
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
    // per module, the manifest that verified it, the flags it records and the module's files
    std::vector<int32_t> verified_by(n, -1);
    std::vector<uint32_t> init_flags(n, 0);
    std::vector<std::vector<std::pair<uint32_t, content_hash>>> files_of(n);
    // whether a manifest lists the module, verified or not: its code is then in that library too
    std::vector<bool> listed(n, false);
    std::vector<std::pair<uint32_t, content_hash>> files;
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
                listed[idx] = true;
                if (packed_module_files(nm, lean_array_get_core(datas, idx), files) && same_files(m, mm, files)) {
                    verified_by[idx] = static_cast<int32_t>(mi);
                    init_flags[idx] = mm.flags;
                    files_of[idx] = files;
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
    //   generates, which belong to both phases) or nothing that its `meta` code uses
    //   (`native_meta_code_safe`), all of the code of its `meta import`s is used, and the `meta`
    //   code of its other direct imports (`meta` code may use only that, which the module system
    //   ensures). The `meta` code of a module whose runtime initializer initializes declarations
    //   must then be entered only where its own analysis starts, at the symbols of its declarations
    //   marked `meta`: by the interpreter (`filter_native_symbol`), and by the native code of the
    //   modules that import it (`native_meta_code_enters_meta`), or else these are interpreted.
    // - The runtime initializers that run early this way, before their module's turn, must run no
    //   `[init]` declarations: they are those of modules that come after it in the import order (a
    //   flag bump of the import can do that).
    // - If its compile-time initializer initializes declarations, which can use the `meta` code of
    //   any module that it imports directly or indirectly, those of these whose compile-time
    //   initializers initialize declarations must come before it, so that these have run, unless
    //   the code that it runs is the module's own or Lean's (`native_meta_init_local`).
    // - A regular import that is not imported (a private import of a module imported for run time
    //   only) is called neither by its `meta` code (the module system lets `meta` code reachable
    //   from other modules use only public imports) nor by its compile-time initializer, if that
    //   initializes nothing or runs only the module's own code and Lean's.
    // - Its native initializers run the `[init]` declarations of each phase in declaration order,
    //   those for run time first, while the interpreter runs all of them in declaration order: all
    //   of its code is used only if it has no `[init]` declarations of one of the phases.
    // - A module whose native initializers ran in an earlier import runs none of its initializers
    //   now (`filter_native_initializer`): its code is used only for the same files and the same
    //   library, all of it only if all of its initializers ran.
    // - Lean's own code of a module that a library has too is used, but not the library's code of
    //   the module's importers, which would use the library's copy.
    // By depth-first search; core modules import only core modules.
    std::vector<int32_t> owner(n, g_not_found - 1);
    auto owner_of_module = [&](size_t x) {
        if (owner[x] < g_not_found) {
            std::string sym = std::string(init_prefix) + init_name(x);
            void * a = dlsym(RTLD_DEFAULT, sym.c_str());
            owner[x] = a ? owner_of(reinterpret_cast<uintptr_t>(a)) : g_not_found;
            if (owner[x] == g_core || owner[x] >= 0) found.emplace(std::move(sym), a);
        }
        return owner[x];
    };
    std::vector<bool> toolchain;
    {
        std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
        generation = g_libs_generation.load();
        for (loaded_lib const & l : *g_libs) toolchain.push_back(l.toolchain);
    }
    // Symbol lookup can see a library loaded after this snapshot. Such owners are not verified by
    // this import, and must not index its per-library data or be recorded as its native initializers.
    auto owner_in_snapshot = [&](int32_t own) {
        return own >= 0 && static_cast<size_t>(own) < toolchain.size();
    };
    lib_of.assign(n, -1);
    meta_only.assign(n, false);
    mods.init_lib.assign(n, -1);
    // 0: not visited, 1: being visited, 2: visited
    std::vector<uint8_t> state(n, 0);
    std::vector<bool> full_ok(n, false), meta_ok(n, false);
    // the greatest index of a module with `[init]` declarations that the module's runtime
    // initializer runs, the module included, and of a module whose compile-time initializer
    // initializes declarations, which it imports directly or indirectly (-1 if none)
    std::vector<int64_t> last_init(n, -1), last_meta_init(n, -1);
    std::vector<bool> meta_inits_of(n, true);
    // whether only the `meta` code of the module is used although its runtime initializer
    // initializes declarations, and whether that holds for a module that it imports directly or
    // indirectly
    std::vector<bool> guarded(n, false), guarded_below(n, false);
    std::vector<std::pair<size_t, size_t>> stack;
    size_t used = 0, used_meta = 0, not_runtime = 0, not_imports = 0, not_order = 0;
    // what the summary of a build gets from this import: the modules of dependencies that run in the
    // interpreter, with why, and those whose code a plugin loaded
    by_import_notes by_import, loaded;
    char const * built = getenv("PAPERLEAN_ROOT_PACKAGE");
    std::vector<char const *> importer_why(n, nullptr);
    auto has_package = [&](size_t x) { return lean_string_size(lean_array_get_core(packages, x)) > 1; };
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
                full_ok[x] = meta_ok[x] = !listed[x];
                continue;
            }
            int64_t self = static_cast<int64_t>(x);
            // (`own` can be a library that another thread loaded after `toolchain` was taken)
            bool verified = owner_in_snapshot(own) &&
                (toolchain[own] || (verified_by[x] >= 0 && ms[verified_by[x]].lib == own));
            // the module's flags, as the manifest records them, or what they can be
            uint32_t flags = verified_by[x] >= 0 ? init_flags[x] : 0;
            bool known = flags & native_init_known;
            bool differs = known ? (flags & native_differs) : lean_unbox(lean_array_get_core(env_differs, x));
            // Code that Lean loaded otherwise (`--load-dynlib`, a plugin) is used as Lean uses it, unless
            // a library has its module too, whose code for the module's importers would use its own
            // copy; a library's code is used only for a module that runs as interpreted.
            bool code_ok = own == g_elsewhere ? !listed[x] : verified && !differs;
            bool runs_init = known ? (flags & native_runtime_init_runs) : lean_unbox(lean_array_get_core(has_init, x));
            bool meta_inits = known ? (flags & native_meta_init_initializes) : true;
            bool runtime_inits = known ? (flags & native_runtime_init_initializes) : true;
            bool meta_safe = known && (flags & native_meta_code_safe);
            bool meta_local = known && (flags & native_meta_init_local);
            bool enters_meta = known && (flags & native_meta_code_enters_meta);
            bool mixed = known ? (flags & native_runtime_init_runs) && (flags & native_meta_init_runs)
                : lean_unbox(lean_array_get_core(mixed_inits, x));
            // a module whose native initializers ran in an earlier import
            bool ran_meta_only = false;
            if (own >= 0) {
                std::string mod = name(lean_array_get_core(names, x), true).to_string();
                std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
                auto it = g_initialized_modules->find(mod);
                if (it != g_initialized_modules->end()) {
                    if (it->second.lib != own || it->second.files != files_of[x] || verified_by[x] < 0) code_ok = false;
                    ran_meta_only = it->second.meta_only;
                }
            }
            meta_inits_of[x] = meta_inits;
            bool full_imports = true, meta_imports = true, early_ok = true;
            char const * import_why = nullptr;
            int64_t last = -1, last_meta = -1;
            for (size_t i = 0; i < array_size(imps); i++) {
                size_t v = lean_unbox(lean_array_get_core(imps, i));
                size_t j = v / 2;
                if (j >= n) {
                    full_imports = false;
                    if (v % 2 || (meta_inits && !meta_local)) meta_imports = false;
                    continue;
                }
                if (owner[j] == g_core && !listed[j]) continue;
                full_imports = full_imports && full_ok[j];
                meta_imports = meta_imports && (v % 2 ? full_ok[j] : meta_ok[j]);
                if (importer_why[j] && import_why != g_imports) import_why = importer_why[j];
                guarded_below[x] = guarded_below[x] || guarded[j] || guarded_below[j];
                // its initializers run the import's runtime initializer
                if (v % 2 || lean_unbox(lean_array_get_core(runtime_init, x))) early_ok = early_ok && last_init[j] < self;
                if (v % 2 == 0) last = std::max(last, last_init[j]);
                last_meta = std::max(last_meta, std::max(meta_inits_of[j] ? static_cast<int64_t>(j) : -1, last_meta_init[j]));
            }
            bool runtime = lean_unbox(lean_array_get_core(runtime_init, x));
            bool order = early_ok && (!meta_inits || meta_local || last_meta < self);
            full_ok[x] = code_ok && runtime && full_imports && order && !mixed && !ran_meta_only;
            meta_ok[x] = full_ok[x] || (code_ok && !runtime && (!runtime_inits || meta_safe) &&
                (enters_meta || !guarded_below[x]) && meta_imports && order);
            guarded[x] = !full_ok[x] && meta_ok[x] && runtime_inits;
            last_init[x] = runs_init ? std::max(last, self) : last;
            last_meta_init[x] = last_meta;
            bool imports_ok = runtime ? full_imports : meta_imports;
            if (own >= 0 && verified_by[x] >= 0 && !meta_ok[x]) {
                // for `PAPERLEAN_IMPORT_TIMING`: why verified modules are not used
                if (!imports_ok) not_imports++;
                else if (!order) not_order++;
                else not_runtime++;
            }
            if (own == g_elsewhere && of_dependency(built, packages, x)) note_by_import(loaded, names, x, g_loaded);
            if (!meta_ok[x]) {
                if (own == g_elsewhere) {
                    // (its code is used as Lean uses it: only what imports it loses something)
                    importer_why[x] = g_imports_plugin;
                } else if (of_dependency(built, packages, x)) {
                    char const * why = verified_by[x] < 0 ? (listed[x] ? g_files_changed : unlisted_why(names, datas, x))
                        : verified && differs ? g_rejected
                        : !code_ok ? g_not_usable
                        : !imports_ok ? (import_why ? import_why : g_import_not_used)
                        : !order ? g_order
                        : mixed ? g_mixed
                        : g_no_runtime_init;
                    // (an importer's code is lost wherever this module's is: `always` carries over)
                    importer_why[x] = why[0] == 'a' ? g_imports : g_imports_here;
                    note_by_import(by_import, names, x, why);
                }
            }
            if (owner_in_snapshot(own) && !toolchain[own] && has_package(x)) mods.init_lib[x] = own;
            if (!owner_in_snapshot(own) || !meta_ok[x]) continue;
            lib_of[x] = own;
            meta_only[x] = !full_ok[x];
            auto init = std::make_shared<native_init const>(native_init{ own, name(lean_array_get_core(names, x), true).to_string(),
                                                                       init_name(x), !full_ok[x], files_of[x] });
            for (char const * prefix : g_init_prefixes)
                if (full_ok[x] || prefix[0] == 'm')
                    inits.emplace(std::string(prefix) + init_name(x), init);
            if (!toolchain[own]) {
                (full_ok[x] ? used : used_meta)++;
                lib_used[verified_by[x]] = true;
            }
        }
    }
    write_by_import(by_import, loaded);
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

// Whether `mods` has a module whose initializer is in one of these libraries.
bool any_init_lib(native_modules const & mods) {
    return std::any_of(mods.init_lib.begin(), mods.init_lib.end(), [](int32_t l) { return l >= 0; });
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
    if (mods) {
        lean_inc(env); lean_inc(fn);
        uint32 idx = lean_paperlean_const_module_idx(env, fn);
        if (idx != 0 && idx - 1 < mods->lib_of.size() && mods->lib_of[idx - 1] == owner) {
            if (!mods->meta_only[idx - 1]) return addr;
            lean_inc(env); lean_inc(fn);
            if (lean_paperlean_is_meta_const(env, fn)) return addr;
        }
    }
    // a module whose native initializers ran in this process: its native code if the module has the
    // same files, otherwise the values of its `[init]` declarations
    lean_inc(env); lean_inc(fn);
    name mod(lean_paperlean_const_module_name(env, fn));
    initialized_module im;
    {
        std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
        auto it = g_initialized_modules->find(mod.to_string());
        if (it == g_initialized_modules->end() || it->second.lib != owner) return nullptr;
        im = it->second;
    }
    lean_inc(env); lean_inc(fn);
    uint32 idx = lean_paperlean_const_module_idx(env, fn);
    object * datas = imports_id(env);
    std::vector<std::pair<uint32_t, content_hash>> files;
    bool same = !im.files.empty() && idx != 0 && idx - 1 < array_size(datas) &&
        packed_module_files(mod.raw(), lean_array_get_core(datas, idx - 1), files) && files == im.files;
    if (!same) {
        // its `[init]` attribute: in the exported attribute entries, or, for a non-`meta` `initialize`
        // of a `module`, only in that module's `.ir` entries (the value the earlier native initializer
        // stored is what a plain import keeps in `g_init_globals`)
        lean_inc(env); lean_inc(fn);
        if (!lean_paperlean_imported_has_init(env, fn, idx)) return nullptr;
    }
    if (im.meta_only) {
        lean_inc(env); lean_inc(fn);
        if (!lean_paperlean_is_meta_const(env, fn)) return nullptr;
    }
    return addr;
#else
    (void)env; (void)fn;
    return addr;
#endif
}

void * found_native_initializer(char const * sym) {
#ifdef PAPERLEAN_NATIVE_LIBS
    if (!g_finalizing || g_finalizing->empty()) return nullptr;
    native_inits const & f = g_finalizing->back();
    if (!f.found || f.generation != g_libs_generation.load()) return nullptr;
    auto it = f.found->find(sym);
    return it == f.found->end() ? nullptr : it->second;
#else
    (void)sym;
    return nullptr;
#endif
}

static std::atomic<bool> g_dynlib_loaded{false};

void note_dynlib_load() { g_dynlib_loaded = true; }

bool skip_native_lookup(b_obj_arg env, b_obj_arg fn) {
#ifdef PAPERLEAN_NATIVE_LIBS
    if (!g_any_loaded.load(std::memory_order_acquire) || g_dynlib_loaded.load()) return false;
    uncounted_heartbeats uncounted;
    lean_object * h = imports_id(env);
    native_modules const * mods = nullptr;
    {
        std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
        auto it = g_native_modules->find(h);
        if (it != g_native_modules->end()) mods = &it->second;
    }
    if (!mods) return false;
    lean_inc(env); lean_inc(fn);
    uint32 idx = lean_paperlean_const_module_idx(env, fn);
    if (idx == 0 || idx - 1 >= mods->init_lib.size()) return false;
    int32_t lib = mods->init_lib[idx - 1];
    if (lib < 0) return false;
    // the code of the module that `filter_native_symbol` keeps: all of it, or its `meta` declarations
    bool meta = mods->lib_of[idx - 1] == lib;
    if (meta && !mods->meta_only[idx - 1]) return false;
    lean_inc(env); lean_inc(fn);
    std::string mod = name(lean_paperlean_const_module_name(env, fn)).to_string();
    {
        std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
        if (g_initialized_modules->count(mod)) return false;
    }
    if (meta) {
        lean_inc(env); lean_inc(fn);
        if (lean_paperlean_is_meta_const(env, fn)) return false;
    }
    return true;
#else
    (void)env; (void)fn;
    return false;
#endif
}

void * filter_native_initializer(char const * sym, void * addr) {
#ifdef PAPERLEAN_NATIVE_LIBS
    if (!g_any_loaded.load(std::memory_order_acquire)) return addr;
    native_inits const * f = g_finalizing && !g_finalizing->empty() ? &g_finalizing->back() : nullptr;
    {
        // an initializer of a module whose native initializers ran in another finalization
        std::shared_lock<std::shared_mutex> lock(g_libs_mutex);
        auto it = g_initialized_inits->find(sym);
        if (it != g_initialized_inits->end() && (!f || g_initialized_modules->at(it->second).serial != f->serial))
            return reinterpret_cast<void *>(&already_initialized);
    }
    if (!addr) return addr;
    int32_t owner = owner_of(reinterpret_cast<uintptr_t>(addr));
    if (owner == g_pulled_in) return nullptr;
    if (owner < 0) return addr;
    if (!f || !f->inits) return nullptr;
    auto it = f->inits->find(sym);
    if (it == f->inits->end() || it->second->lib != owner) return nullptr;
    native_init const & init = *it->second;
    std::unique_lock<std::shared_mutex> lock(g_libs_mutex);
    if (g_initialized_modules->emplace(init.module, initialized_module{ owner, init.meta_only, init.files, f->serial }).second)
        for (char const * prefix : g_init_prefixes)
            g_initialized_inits->emplace(std::string(prefix) + init.init_name, init.module);
    return addr;
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

#ifdef PAPERLEAN_NATIVE_LIBS
// The dependency modules of the import of `env`, for an import without native libraries.
static void note_unprepared(b_obj_arg env) {
    lean_inc(env);
    object_ref info(lean_paperlean_import_packages(env));
    object * names = cnstr_get(info.raw(), 0);
    object * packages = cnstr_get(info.raw(), 1);
    by_import_notes notes, loaded;
    char const * built = getenv("PAPERLEAN_ROOT_PACKAGE");
    object * datas = imports_id(env);
    // (it stops at the limit, and `write_by_import` then says that this is not all)
    for (size_t x = 0; x < array_size(names) && notes.size() <= g_max_by_import; x++) {
        if (!of_dependency(built, packages, x)) continue;
        // (code that a plugin or a shared library loaded is used, as `verify` finds: `g_elsewhere`)
        lean_inc(env);
        object_ref symbol(lean_paperlean_module_init_symbol(env, lean_box(x)));
        if (dlsym(RTLD_DEFAULT, lean_string_cstr(symbol.raw()))) note_by_import(loaded, names, x, g_loaded);
        else note_by_import(notes, names, x, x < array_size(datas) ? unlisted_why(names, datas, x) : g_no_library);
    }
    write_by_import(notes, loaded);
}

#endif

/* loadNativeLibs (env : @& Environment) (opts : @& Options) : BaseIO Unit */
extern "C" LEAN_EXPORT obj_res lean_paperlean_load_native_libs(b_obj_arg env, b_obj_arg opts) {
#ifdef PAPERLEAN_NATIVE_LIBS
    // PaperLean's work, not counted as heartbeats
    uncounted_heartbeats uncounted;
    char const * list = getenv("PAPERLEAN_NATIVE_LIBS");
    if (!list || !*list) {
        // (no library verifies anything; the question is asked only for a build that wants the answer)
        if (getenv("PAPERLEAN_ROOT_PACKAGE") && getenv("PAPERLEAN_NATIVE_STATS")) note_unprepared(env);
        return lean_box(0);
    }
    lean_object * h = imports_id(env);
    if (!g_finalizing) g_finalizing = new std::vector<native_inits>();
    g_finalizing->push_back({ h, nullptr, nullptr, 0, ++g_finalizations });
    // only for imports that are never freed, which their module data identifies for good
    if (lean_is_scalar(h) || !lean_is_persistent(h)) return lean_box(0);
    try {
        native_modules mods;
        auto * inits = new std::unordered_map<std::string, std::shared_ptr<native_init const>>();
        auto * found = new std::unordered_map<std::string, void *>();
        g_finalizing->back().found = found;
        uint64_t generation = 0;
        bool used = verify(env, opts, list, mods, *inits, *found, generation);
        g_finalizing->back().generation = generation;
        if (used || any_init_lib(mods)) {
            std::unique_lock<std::shared_mutex> lock(g_libs_mutex);
            g_native_modules->emplace(h, std::move(mods));
        }
        if (used) g_finalizing->back().inits = inits;
        else delete inits;
    } catch (std::exception & ex) {
        side_file_warning("warning: not using native libraries: %s\n", ex.what());
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
        delete g_finalizing->back().found;
        g_finalizing->pop_back();
    }
    return lean_box(0);
}

#ifdef PAPERLEAN_NATIVE_LIBS
namespace {
// The top-level definitions of a `.c` file that `EmitC.lean` wrote, functions and variables, with the
// ranges of their bodies and initializers, and the names it declares without defining them.
struct c_unit {
    std::string text;
    std::unordered_map<std::string_view, std::pair<size_t, size_t>> defs;
    std::unordered_set<std::string_view> statics;   // those of `defs` that other files cannot name
    std::unordered_set<std::string_view> decls;
};

bool is_ident_start(char c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'; }
bool is_ident(char c) { return is_ident_start(c) || (c >= '0' && c <= '9'); }

// Calls `f` with the position after each token of `t[i, end)`: an identifier (`f(b, e)`), or another
// character (`f(i, i)`, with `t[i]` that character), skipping comments, string and character literals
// and preprocessor lines.
template<class F> void for_each_token(std::string const & t, size_t i, size_t end, F && f) {
    while (i < end) {
        char c = t[i];
        if (c == '#' && (i == 0 || t[i - 1] == '\n')) {
            while (i < end && t[i] != '\n') i += t[i] == '\\' ? 2 : 1;
        } else if (c == '/' && i + 1 < end && t[i + 1] == '/') {
            while (i < end && t[i] != '\n') i++;
        } else if (c == '/' && i + 1 < end && t[i + 1] == '*') {
            size_t e = t.find("*/", i + 2);
            i = e == std::string::npos ? end : e + 2;
        } else if (c == '"' || c == '\'') {
            for (i++; i < end && t[i] != c; i += t[i] == '\\' ? 2 : 1) {}
            if (i < end) f(i, i);
            i++;
        } else if (is_ident_start(c)) {
            size_t b = i;
            while (i < end && is_ident(t[i])) i++;
            f(b, i);
        } else {
            if (c != ' ' && c != '\n' && c != '\t' && c != '\r') f(i, i);
            i++;
        }
    }
}

// Reads and parses the `.c` file `path`.
bool read_c_unit(char const * path, c_unit & u) {
    FILE * f = fopen(path, "rb");
    if (!f) return false;
    char buf[1 << 16];
    for (size_t r; (r = fread(buf, 1, sizeof(buf), f)) > 0;) u.text.append(buf, r);
    fclose(f);
    std::string const & t = u.text;
    // the current top-level item: its last identifier, that before its first `(`, that before its
    // `=`, and whether it is `extern`
    std::string_view last, before_paren, before_eq;
    bool paren = false, eq = false, ext = false, quoted = false, fn = false, is_static = false;
    size_t init_start = 0, body_start = 0;
    int depth = 0;
    auto reset = [&] { last = before_paren = before_eq = {}; paren = eq = ext = quoted = fn = is_static = false; };
    auto define = [&](std::string_view n, std::pair<size_t, size_t> range) {
        u.defs[n] = range;
        if (is_static) u.statics.insert(n);
    };
    for_each_token(t, 0, t.size(), [&](size_t b, size_t e) {
        if (b != e) {
            if (depth == 0) {
                last = std::string_view(t.data() + b, e - b);
                if (last == "extern") ext = true;
                if (last == "static") is_static = true;
            }
            return;
        }
        char c = t[b];
        if (depth == 0 && (c == '"' || c == '\'')) { quoted = true; return; }
        if (c == '{') {
            // `extern "C" {` (without the preprocessor's help)
            if (depth == 0 && ext && quoted && !paren && !eq) { reset(); return; }
            if (depth == 0 && paren && !eq) { fn = true; body_start = b + 1; }
            depth++;
        } else if (c == '}') {
            if (depth == 0) return;
            if (--depth == 0 && fn) {
                define(before_paren, { body_start, b });
                reset();
            }
        } else if (depth == 0) {
            if (c == '(' && !paren && !eq) { paren = true; before_paren = last; }
            else if (c == '=' && !paren && !eq) { eq = true; before_eq = last; init_start = b + 1; }
            else if (c == ';') {
                if (eq) define(before_eq, { init_start, b });
                else if (paren) u.decls.insert(before_paren);
                else if (ext) u.decls.insert(last);
                else if (!last.empty()) define(last, { b, b });
                reset();
            }
        }
    });
    return true;
}

// The functions that Lean's `lean.h` defines or declares (`EmitC.lean` declares some of the former
// again).
std::unordered_set<std::string> const & lean_header_names() {
    static std::unordered_set<std::string> names = [] {
        std::unordered_set<std::string> r;
        c_unit h;
        if (!lean_lib_dir().empty() && read_c_unit((dir_of(dir_of(lean_lib_dir())) + "/include/lean/lean.h").c_str(), h)) {
            for (auto const & d : h.defs) r.emplace(d.first);
            for (auto const & d : h.decls) r.emplace(d);
        }
        return r;
    }();
    return names;
}

// Whether `sym` is a symbol of Lean's own code, which is initialized when Lean starts: of `lean.h`,
// or of `libleanshared` or `libInit_shared` as this process finds it.
bool lean_own_symbol(std::string const & sym) {
    static std::mutex mutex;
    static std::unordered_map<std::string, bool> known;
    static std::unordered_map<std::string, bool> lean_image;
    if (lean_header_names().count(sym)) return true;
    std::lock_guard<std::mutex> lock(mutex);
    auto it = known.find(sym);
    if (it != known.end()) return it->second;
    bool own = false;
    Dl_info info;
    if (void * a = dlsym(RTLD_DEFAULT, sym.c_str()); a && dladdr(a, &info) && info.dli_fname) {
        auto im = lean_image.find(info.dli_fname);
        if (im == lean_image.end()) {
            std::string path;
            im = lean_image.emplace(info.dli_fname, is_lean_lib(info.dli_fname, path) && is_core_lib(path)).first;
        }
        own = im->second;
    }
    known.emplace(sym, own);
    return own;
}

// Whether something in this process defines `sym`, as Lean's `lean.h` and libraries do when they are
// what it is linked against.
bool defined_here(std::string const & sym) {
    // The guarded standard spellings are bound to toolchain entry points even when a system
    // libc does not expose the unprefixed spelling in RTLD_DEFAULT. Never create a stub for
    // them or allow a package to claim their names.
    return native_math(sym) || lean_header_names().count(sym) || dlsym(RTLD_DEFAULT, sym.c_str());
}

// The body of the initializer `<prefix>initialize_...` that `u` defines, if it defines one.
bool init_body(c_unit const & u, char const * prefix, std::pair<size_t, size_t> & body) {
    std::string head = std::string(prefix) + "initialize_";
    size_t found = 0;
    for (auto const & d : u.defs)
        if (d.first.substr(0, head.size()) == head && d.second.first < d.second.second) { body = d.second; found++; }
    return found == 1;
}

// The identifiers that the statements of the initializer body `body` of `u` use, except for the calls
// of its imports' initializers.
std::vector<std::string_view> init_uses(c_unit const & u, std::pair<size_t, size_t> body) {
    std::string const & t = u.text;
    std::vector<std::string_view> ids;
    for (size_t p = body.first; p < body.second;) {
        size_t q = std::min(t.find('\n', p), body.second);
        std::string_view l(t.data() + p, q - p);
        bool import_init = l.substr(0, 6) == "res = " && l.size() >= 10 && l.substr(l.size() - 10) == "(builtin);" &&
            l.find("initialize_") != std::string_view::npos;
        if (!import_init)
            for_each_token(t, p, q, [&](size_t b, size_t e) { if (b != e) ids.push_back(std::string_view(t.data() + b, e - b)); });
        p = q + 1;
    }
    return ids;
}

// Visits what the identifiers `roots` use, directly or through the definitions of `u`: `defined(id)`
// for a definition of `u`, `external(id)` for a name that `u` declares without defining it (other
// identifiers are of `lean.h` or local); stops when one returns `false`, and returns whether none
// did.
template<class D, class E> bool for_each_used(c_unit const & u, std::vector<std::string_view> roots, D && defined, E && external) {
    std::string const & t = u.text;
    std::unordered_set<std::string_view> seen;
    while (!roots.empty()) {
        std::string_view id = roots.back();
        roots.pop_back();
        if (!seen.insert(id).second) continue;
        auto d = u.defs.find(id);
        if (d != u.defs.end()) {
            if (!defined(id)) return false;
            for_each_token(t, d->second.first, d->second.second, [&](size_t b, size_t e) {
                if (b != e) roots.push_back(std::string_view(t.data() + b, e - b));
            });
        } else if (u.decls.count(id) && !external(id)) {
            return false;
        }
    }
    return true;
}

// Whether the code that the compile-time initializer of the module of `u` runs is the module's own or
// Lean's: what the initializer's statements other than its frame and the calls of its imports'
// initializers use, directly or through the module's definitions, is defined in `u` or is Lean's
// own (`lean.h`, or a declared symbol of Lean's own code).
bool meta_init_local(c_unit const & u) {
    std::pair<size_t, size_t> body;
    if (!init_body(u, "meta_", body)) return false;
    return for_each_used(u, init_uses(u, body), [](std::string_view) { return true; },
                         [](std::string_view id) { return lean_own_symbol(std::string(id)); });
}

// The flags `native_meta_code_safe` and `native_meta_code_enters_meta` of the module of `u`, whose
// `meta` declarations have the symbols `own` (`ModuleNativeData.metaSymbols`), with those of other
// modules in `all`.
uint32_t meta_code_flags(c_unit const & u, object * own, std::unordered_set<std::string> const & all) {
    std::pair<size_t, size_t> meta_body, runtime_body;
    if (!init_body(u, "meta_", meta_body) || !init_body(u, "runtime_", runtime_body)) return 0;
    // the declarations that the runtime initializer initializes
    std::unordered_set<std::string_view> initialized;
    std::string const & t = u.text;
    for (size_t p = runtime_body.first; p < runtime_body.second;) {
        size_t q = std::min(t.find('\n', p), runtime_body.second);
        size_t e = p;
        while (e < q && is_ident(t[e])) e++;
        if (e > p && t.compare(e, 3, " = ") == 0) {
            std::string_view id(t.data() + p, e - p);
            if (id != "res" && u.defs.count(id)) initialized.insert(id);
        }
        p = q + 1;
    }
    std::vector<std::string_view> roots = init_uses(u, meta_body);
    for (size_t i = 0; i < lean_array_size(own); i++) {
        std::string_view sym(lean_string_cstr(lean_array_get_core(own, i)), lean_string_size(lean_array_get_core(own, i)) - 1);
        auto d = u.defs.find(sym);
        if (d != u.defs.end()) roots.push_back(d->first);
    }
    bool reads_initialized = false;
    bool enters_meta = for_each_used(u, roots,
        [&](std::string_view id) { if (initialized.count(id)) reads_initialized = true; return true; },
        [&](std::string_view id) { std::string s(id); return all.count(s) || lean_own_symbol(s); });
    if (!enters_meta) return 0;
    return native_meta_code_enters_meta | (reads_initialized ? 0 : native_meta_code_safe);
}

// The flags `native_runtime_init_runs`, `native_meta_init_initializes`,
// `native_runtime_init_initializes` and `native_meta_init_runs` of the module whose `.c` file
// (`EmitC.lean`) is `path`: a
// statement of an initializer that is not part of its frame, a call of an import's initializer or a
// builtin initialization (which `runInitAttrForMod` does not run) runs an `[init]` declaration
// (`res = ...`) or initializes a declaration. A file without initializers for the phases has only
// the one for all phases.
bool c_init_flags(c_unit const & u, uint32_t & flags) {
    std::string const & c = u.text;
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
        (meta_inits ? native_meta_init_initializes : 0) | (runtime_inits ? native_runtime_init_initializes : 0) |
        (meta_runs ? native_meta_init_runs : 0);
    return true;
}
}
#endif

// EmitC assigns a foreign scalar call to an SSA variable and only passes SSA variables.
// Restrict the five reserved names to such calls and the exact prototype above; a definition,
// incompatible redeclaration, function pointer, or address-taking does not satisfy this test.
static bool native_math_call(std::string_view line, native_math_op const & op) {
    auto take = [&](std::string_view prefix) {
        if (line.substr(0, prefix.size()) != prefix) return false;
        line.remove_prefix(prefix.size()); return true;
    };
    auto var = [&]() {
        if (!take("v_")) return false;
        size_t i = 0;
        for (; i < line.size(); ++i) {
            char c = line[i];
            if (!(c == '_' || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
                    (c >= '0' && c <= '9'))) break;
        }
        line.remove_prefix(i); return i != 0;
    };
    return var() && take(" = ") && take(op.name) && take("(") && var() &&
        (op.arity == 1 || (take(", ") && var())) && line == ");";
}

// Only this positive subset of EmitC's output is eligible for location-independent native code.
// The body has no preprocessing directives. The admitted headers/macros and identifier families
// are from lean.h and EmitC; an arbitrary extern expression or C extension is not assumed safe.
static bool portable_emitted_c(std::string_view text,
        std::unordered_set<std::string_view> const * declared = nullptr,
        std::unordered_set<std::string_view> * used = nullptr) {
    auto take = [&](std::string_view s) {
        if (text.substr(0, s.size()) != s) return false;
        text.remove_prefix(s.size());
        return true;
    };
    // Splicing and trigraph substitution happen before the C lexer sees comments and literals.
    if (text.find("??") != text.npos || text.find('\r') != text.npos || text.find('\0') != text.npos) return false;
    for (size_t p = text.find('\\'); p != text.npos; p = text.find('\\', p + 1)) {
        size_t q = text.find_first_not_of(" \t\v\f", p + 1);
        if (q == text.npos || text[q] == '\n') return false;
    }
    if (!take("// Lean compiler output\n")) return false;
    for (auto prefix : {"// Module: ", "// Imports:"}) {
        if (!take(prefix)) return false;
        size_t line = text.find('\n');
        if (line == text.npos) return false;
        text.remove_prefix(line + 1);
    }
    if (!take("#include <lean/lean.h>\n"
              "#if defined(__clang__)\n"
              "#pragma clang diagnostic ignored \"-Wunused-parameter\"\n"
              "#pragma clang diagnostic ignored \"-Wunused-label\"\n"
              "#elif defined(__GNUC__) && !defined(__CLANG__)\n"
              "#pragma GCC diagnostic ignored \"-Wunused-parameter\"\n"
              "#pragma GCC diagnostic ignored \"-Wunused-label\"\n"
              "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"\n"
              "#endif\n#ifdef __cplusplus\nextern \"C\" {\n#endif\n")) return false;
    constexpr std::string_view footer = "#ifdef __cplusplus\n}\n#endif\n";
    if (text.size() < footer.size() || text.substr(text.size() - footer.size()) != footer) return false;
    text.remove_suffix(footer.size());
    static std::unordered_set<std::string_view> const fixed {
        "LEAN_EXPORT", "LEAN_ONCE_CELL_INITIALIZER", "LEAN_SCALAR_PTR_LITERAL", "LEAN_ALWAYS_INLINE",
        "LEAN_UNLIKELY", "LEAN_LIKELY", "LEAN_BYTE", "LeanClosure", "LeanString", "LeanArray", "LeanScalarArray",
        "bool", "char", "const", "double", "extern", "float", "int", "int8_t", "int16_t", "int32_t",
        "int64_t", "intptr_t", "long", "short", "signed", "size_t", "static", "struct", "uint8_t",
        "uint16_t", "uint32_t", "uint64_t", "uintptr_t", "unsigned", "void", "break", "case",
        "default", "do", "else", "false", "for", "goto", "if", "return", "sizeof", "switch", "true",
        "while", "NULL", "builtin", "res", "_start", "_args", "_aargs", "_result",
        // Ground constants use designated initializers of the fixed runtime structs.
        "m_header", "m_rc", "m_tag", "m_other", "m_cs_sz", "m_size", "m_capacity", "m_length",
        "m_data", "m_objs", "m_value", "m_fun", "m_arity", "m_num_fixed", "m_y"
    };
    unsigned math_decls = 0;
    auto known = [&](std::string_view id, size_t begin) {
        // New definitions of the tools' binding targets are not package symbols.
        if (id.substr(0, g_math_prefix.size()) == g_math_prefix) return false;
        for (std::string_view p : {"lean_", "l_", "lp_", "v_", "_G_", "_init_", "_tmp_",
                "initialize_", "runtime_initialize_", "meta_initialize_"})
            if (id.substr(0, p.size()) == p) return true;
        if (fixed.count(id)) return true;
        if (!declared) return false;
        if (auto * op = native_math(id)) {
            auto start = text.rfind('\n', begin), end = text.find('\n', begin);
            start = start == text.npos ? 0 : start + 1;
            std::string_view line = text.substr(start, end - start);
            unsigned bit = 1u << static_cast<unsigned>(op - g_math_ops);
            if (line == op->prototype) math_decls |= bit;
            else if (!(math_decls & bit) || !native_math_call(line, *op)) return false;
        } else if (!declared->count(id)) return false;
        if (used) used->insert(id);
        return true;
    };
    auto letter = [](char c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'; };
    auto digit = [](char c) { return c >= '0' && c <= '9'; };
    for (size_t i = 0; i < text.size();) {
        char c = text[i++];
        if (letter(c)) {
            size_t b = i - 1;
            while (i < text.size() && (letter(text[i]) || digit(text[i]))) ++i;
            if (!known(text.substr(b, i - b), b)) return false;
        } else if (digit(c)) {
            while (i < text.size() && (letter(text[i]) || digit(text[i]) || text[i] == '.')) ++i;
        } else if (c == '"') {
            bool closed = false;
            while (i < text.size() && text[i] != '\n') {
                char ch = text[i++];
                if (ch == c) { closed = true; break; }
                if (ch == '\\' && i < text.size()) ++i;
            }
            if (!closed) return false;
        } else if (c == '/' && text.substr(i, 1) == "/") {
            i = text.find('\n', i);
            if (i == text.npos) return false;
        } else if (c == '/' && text.substr(i, 1) == "*") {
            i = text.find("*/", i + 1);
            if (i == text.npos) return false;
            i += 2;
        } else if (std::string_view(" \t\v\f\n+-(){}[];,:.*&=!<>/|^~%?").find(c) == text.npos ||
                   (c == '%' && (text.substr(i, 1) == ":" || text.substr(i, 1) == ">")) ||
                   (c == '<' && (text.substr(i, 1) == "%" || text.substr(i, 1) == ":")) ||
                   (c == ':' && text.substr(i, 1) == ">")) {
            return false;
        }
    }
    return true;
}

/* portableEmittedC: the original bytes, after verification against the module trace. */
extern "C" LEAN_EXPORT uint8_t lean_paperlean_portable_emitted_c(b_obj_arg bytes) {
    auto * data = reinterpret_cast<char const *>(lean_sarray_cptr(bytes));
    return portable_emitted_c(std::string_view(data, lean_sarray_size(bytes)));
}

// Additional names come only from the verified module's standard extern/export attributes.
// Keep reserved extensions and C keywords out even when a declaration claims such a name.
static bool custom_c_symbol(std::string_view name) {
    auto alpha = [](char c) { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'); };
    if (name.empty() || !alpha(name.front()) || name.find("__") != name.npos) return false;
    for (char c : name) if (!alpha(c) && !(c >= '0' && c <= '9') && c != '_') return false;
    static std::unordered_set<std::string_view> const reserved {
        "alignas", "alignof", "asm", "auto", "bool", "break", "case", "char", "const", "constexpr",
        "continue", "default", "do", "double", "else", "enum", "extern", "false", "float", "for",
        "goto", "if", "inline", "int", "long", "nullptr", "register", "restrict", "return", "short",
        "signed", "sizeof", "static", "static_assert", "struct", "switch", "thread_local", "true",
        "typedef", "typeof", "typeof_unqual", "union", "unsigned", "void", "volatile", "while"
    };
    return !reserved.count(name);
}

/* Return a forced header for verified C with extra identifiers. Module-owned externs must
remain ordinary external spellings. The fixed Init math operations instead bind to the toolchain.
An included header or preprocessing line still fails the same grammar; no C bytes are rewritten. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_portable_c_symbol_guard(b_obj_arg bytes, b_obj_arg syms) {
    std::unordered_set<std::string_view> declared;
    for (size_t i = 0; i < lean_array_size(syms); ++i) {
        b_obj_arg sym = lean_array_get_core(syms, i);
        std::string_view name(lean_string_cstr(sym), lean_string_size(sym) - 1);
        if (custom_c_symbol(name)) declared.insert(name);
    }
    auto * data = reinterpret_cast<char const *>(lean_sarray_cptr(bytes));
    std::unordered_set<std::string_view> used;
    if (!portable_emitted_c(std::string_view(data, lean_sarray_size(bytes)), &declared, &used))
        return mk_option_none();
    // Cache admission depends on the identifiers in these C bytes. An unused attribute must
    // not change whether identical C compiles on a cold miss or reuses a retained object.
    std::string guard = "#include <lean/lean.h>\n";
    std::vector<std::string_view> ordered(used.begin(), used.end());
    std::sort(ordered.begin(), ordered.end());
    if (std::any_of(ordered.begin(), ordered.end(), [](auto n) { return !native_math(n); }))
        guard += "#ifndef __has_builtin\n#error PaperLean requires a compiler builtin probe\n#endif\n";
    for (std::string_view name : ordered) {
        guard += "#ifdef "; guard += name; guard += "\n#error PaperLean external name is a macro\n#endif\n";
        if (auto * op = native_math(name)) {
            // An asm label gives the original, trace-bound EmitC prototype a fixed linker
            // symbol without redefining a token for the rest of a grouped translation unit.
            guard += "extern "; guard += op->prototype.substr(0, op->prototype.size() - 1);
            guard += " __asm__(\"";
#ifdef __APPLE__
            guard += "_";
#endif
            guard += g_math_prefix; guard += name; guard += "\");\n";
            continue;
        }
        guard += "#ifdef __has_builtin\n#if __has_builtin("; guard += name;
        guard += ")\n#error PaperLean external name is a compiler builtin\n#endif\n#endif\n";
    }
    return mk_option_some(lean_mk_string_from_bytes(guard.data(), guard.size()));
}

#ifdef PAPERLEAN_NATIVE_LIBS
namespace {
using c_names = std::unordered_set<std::string>;

bool init_flag(std::string_view n) {
    return n == "_G_initialized" || n == "_G_runtime_initialized" || n == "_G_meta_initialized";
}

struct grouped_names {
    c_names references, local, definitions, init_flags;
};

// EmitC writes one simple named variable or function per top-level declaration. Reject an unfamiliar
// declarator for grouping: standalone compilation still uses the checked C. Private names must not
// appear even as references in another member, where a merged C translation unit could bind them.
bool group_declarator(std::vector<std::string_view> const & h, char end, grouped_names & names) {
    size_t i = 0;
    bool local = i < h.size() && h[i] == "static";
    bool external = i < h.size() && h[i] == "extern";
    if (local || external || (i < h.size() && h[i] == "LEAN_EXPORT")) ++i;
    if (i < h.size() && h[i] == "const") ++i;
    if (i >= h.size() || !is_ident_start(h[i][0])) return false;
    auto type = h[i++];
    while (i < h.size() && h[i] == "*") ++i;
    if (i >= h.size() || !is_ident_start(h[i][0])) return false;
    std::string name(h[i++]);
    bool function = i < h.size();
    if (function) {
        if (h[i] != "(" || h.back() != ")" || end == '=') return false;
        for (++i; i + 1 < h.size(); ++i)
            if (!is_ident_start(h[i][0]) && h[i] != "*" && h[i] != ",") return false;
    } else if (end == '{') {
        return false;
    }
    if (init_flag(name)) {
        if (!local || function || type != "bool" || end != '=') return false;
        names.init_flags.insert(name);
    } else {
        if (local) names.local.insert(name);
        if (end == '{' || end == '=' || (!external && !function)) names.definitions.insert(name);
    }
    return true;
}

bool group_names(char const * path, grouped_names & names) {
    FILE * f = fopen(path, "rb");
    if (!f) return false;
    std::string text;
    char buf[1 << 16];
    for (size_t n; (n = fread(buf, 1, sizeof(buf), f));) text.append(buf, n);
    bool ok = !ferror(f);
    fclose(f);
    if (!ok) return false;
    constexpr std::string_view opening = "extern \"C\" {\n#endif\n";
    constexpr std::string_view closing = "#ifdef __cplusplus\n}\n#endif\n";
    size_t begin = text.find(opening, text.find("\n#include <lean/lean.h>\n"));
    if (begin == text.npos || text.size() < closing.size()) return false;
    begin += opening.size();
    size_t end = text.size() - closing.size();
    if (begin > end || text.compare(end, closing.size(), closing) != 0) return false;
    enum {header, function_body, initializer} mode = header;
    int braces = 0, parens = 0, brackets = 0;
    std::vector<std::string_view> tokens;
    for_each_token(text, begin, end, [&](size_t b, size_t e) {
        if (!ok) return;
        bool ident = e != b;
        std::string_view tok(text.data() + b, ident ? e - b : 1);
        if (ident) {
            if (tok.substr(0, 3) == "_G_" && !init_flag(tok)) { ok = false; return; }
            names.references.emplace(tok);
        }
        char c = ident ? 0 : text[b];
        if (mode == header) {
            if (c != '{' && c != '=' && c != ';') { tokens.push_back(tok); return; }
            if (!group_declarator(tokens, c, names)) { ok = false; return; }
            tokens.clear();
            if (c == '{') { mode = function_body; braces = 1; }
            if (c == '=') mode = initializer;
            return;
        }
        if (c == '{') ++braces;
        if (c == '}') --braces;
        if (mode == function_body) {
            if (braces == 0) mode = header;
            return;
        }
        if (c == '(') ++parens;
        if (c == ')') --parens;
        if (c == '[') ++brackets;
        if (c == ']') --brackets;
        if (braces < 0 || parens < 0 || brackets < 0) ok = false;
        if (braces == 0 && parens == 0 && brackets == 0) {
            if (c == ',') ok = false; // Another declarator following an initializer.
            if (c == ';') mode = header;
        }
    });
    if (!ok || mode != header || !tokens.empty()) return false;
    for (auto const & s : names.references)
        if (init_flag(s) && !names.init_flags.count(s)) return false;
    return true;
}

bool intersect(c_names const & a, c_names const & b) {
    for (auto const & n : a) if (b.count(n)) return true;
    return false;
}
}
#endif

extern "C" LEAN_EXPORT obj_res lean_paperlean_can_group_checked_c(b_obj_arg paths) {
#ifdef PAPERLEAN_NATIVE_LIBS
    grouped_names all;
    for (size_t i = 0; i < lean_array_size(paths); ++i) {
        grouped_names next;
        if (!group_names(lean_string_cstr(lean_array_get_core(paths, i)), next) ||
            intersect(next.local, all.references) || intersect(all.local, next.references) ||
            intersect(next.definitions, all.definitions))
            return io_result_mk_ok(lean_box(0));
        all.references.insert(next.references.begin(), next.references.end());
        all.local.insert(next.local.begin(), next.local.end());
        all.definitions.insert(next.definitions.begin(), next.definitions.end());
    }
    return io_result_mk_ok(lean_box(1));
#else
    (void)paths;
    return io_result_mk_ok(lean_box(0));
#endif
}

/* cObjectNames (c : @& String) : IO (Array String × Array String × Array String)
   The names of the variables that the `.c` file `c` (`EmitC.lean`) declares as `extern lean_object*`,
   of those that it defines as `const lean_object*`, and of all variables that it defines with
   `LEAN_EXPORT`: a declaration of the first kind and a definition of the second of the same name
   cannot be in one translation unit, and two definitions of the third kind would be one variable
   there (tentative definitions), while they are two symbols that cannot be linked together otherwise. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_c_object_names(b_obj_arg oc) {
    FILE * f = fopen(lean_string_cstr(oc), "rb");
    if (!f) return io_result_mk_error((sstream() << "cannot read " << lean_string_cstr(oc)).str().c_str());
    std::string t;
    char buf[1 << 16];
    for (size_t r; (r = fread(buf, 1, sizeof(buf), f)) > 0;) t.append(buf, r);
    bool ok = !ferror(f);
    fclose(f);
    if (!ok) return io_result_mk_error((sstream() << "cannot read " << lean_string_cstr(oc)).str().c_str());
    object * ext = lean_mk_empty_array();
    object * consts = lean_mk_empty_array();
    object * exported = lean_mk_empty_array();
    // the identifier that ends right before `end`
    auto ident_before = [&](size_t end) {
        size_t b = end;
        while (b > 0 && (isalnum(static_cast<unsigned char>(t[b - 1])) || t[b - 1] == '_')) b--;
        return t.substr(b, end - b);
    };
    for (size_t p = 0; p < t.size();) {
        size_t q = t.find('\n', p);
        if (q == std::string::npos) q = t.size();
        std::string_view l(t.data() + p, q - p);
        if (l.substr(0, 20) == "extern lean_object* " && l.size() > 20 && l.back() == ';' &&
            l.find('(') == std::string_view::npos) {
            ext = lean_array_push(ext, lean_mk_string(ident_before(q - 1).c_str()));
        } else if (l.substr(0, 12) == "LEAN_EXPORT ") {
            // a variable: `LEAN_EXPORT <type> <name>;` or `... <name> = <value>;`
            size_t eq = l.find(" = ");
            size_t paren = l.find('(');
            if (eq != std::string_view::npos && (paren == std::string_view::npos || paren > eq)) {
                std::string n = ident_before(p + eq);
                exported = lean_array_push(exported, lean_mk_string(n.c_str()));
                if (l.substr(0, 31) == "LEAN_EXPORT const lean_object* ") consts = lean_array_push(consts, lean_mk_string(n.c_str()));
            } else if (paren == std::string_view::npos && !l.empty() && l.back() == ';') {
                exported = lean_array_push(exported, lean_mk_string(ident_before(q - 1).c_str()));
            }
        }
        p = q + 1;
    }
    object * inner = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(inner, 0, consts);
    lean_ctor_set(inner, 1, exported);
    object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, ext);
    lean_ctor_set(r, 1, inner);
    return io_result_mk_ok(r);
}

/* copyString (s : @& String) : String -- a new string object with the characters of `s` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_copy_string(b_obj_arg s) {
    return lean_mk_string_from_bytes(lean_string_cstr(s), lean_string_size(s) - 1);
}

/* cSymbols (c : @& String) : IO (Array String × Array String)
   The names of the functions and variables that the `.c` file `c` (`EmitC.lean`) defines for other
   files, and those that it declares without defining them. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_c_symbols(b_obj_arg oc) {
#ifdef PAPERLEAN_NATIVE_LIBS
    c_unit u;
    if (!read_c_unit(lean_string_cstr(oc), u))
        return io_result_mk_error((sstream() << "cannot read " << lean_string_cstr(oc)).str().c_str());
    object * defined = lean_mk_empty_array();
    object * declared = lean_mk_empty_array();
    auto str = [](std::string_view s) { return lean_mk_string_from_bytes(s.data(), s.size()); };
    for (auto const & d : u.defs)
        if (!u.statics.count(d.first)) defined = lean_array_push(defined, str(d.first));
    for (std::string_view d : u.decls)
        if (!u.defs.count(d)) declared = lean_array_push(declared, str(d));
    object * r = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(r, 0, defined);
    lean_ctor_set(r, 1, declared);
    return io_result_mk_ok(r);
#else
    (void)oc;
    return io_result_mk_error("cSymbols: native libraries are supported only on Linux and macOS");
#endif
}

/* undefinedSymbols (names libs : @& Array String) : IO (Array String)
   Those of `names` that neither the libraries `libs` (with those they are linked against), nor
   `lean.h`, nor what this process is linked against define. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_undefined_symbols(b_obj_arg onames, b_obj_arg olibs) {
#ifdef PAPERLEAN_NATIVE_LIBS
    std::vector<void *> handles;
    object * out = lean_mk_empty_array();
    for (size_t i = 0; i < lean_array_size(olibs); i++) {
        void * h = dlopen(lean_string_cstr(lean_array_get_core(olibs, i)), RTLD_LAZY | RTLD_LOCAL);
        if (h) handles.push_back(h);
    }
    for (size_t i = 0; i < lean_array_size(onames); i++) {
        object * n = lean_array_get_core(onames, i);
        char const * sym = lean_string_cstr(n);
        if (defined_here(sym) || std::any_of(handles.begin(), handles.end(), [&](void * h) { return dlsym(h, sym); }))
            continue;
        lean_inc(n);
        out = lean_array_push(out, n);
    }
    for (void * h : handles) dlclose(h);
    return io_result_mk_ok(out);
#else
    (void)onames; (void)olibs;
    return io_result_mk_error("undefinedSymbols: native libraries are supported only on Linux and macOS");
#endif
}

/* loadError (lib : @& String) : IO String
   Why Lean cannot load the library `lib`, as `load_lib` does, or "" if it can. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_load_error(b_obj_arg olib) {
#ifdef PAPERLEAN_NATIVE_LIBS
    void * h = dlopen(lean_string_cstr(olib), RTLD_NOW | RTLD_LOCAL);
    char const * err = h ? nullptr : dlerror();
    std::string why = h ? "" : (err ? err : "it cannot be loaded");
    if (h) dlclose(h);
    return io_result_mk_ok(lean_mk_string_from_bytes(why.data(), why.size()));
#else
    (void)olib;
    return io_result_mk_error("loadError: native libraries are supported only on Linux and macOS");
#endif
}

/* writeNativeManifestFiles (out lib : @& String) (deps : @& Array String)
     (modules : @& Array NativeManifestModule) (extSymbols : @& Array String) : IO (Array String)
   Writes the manifest of the native library `lib` of `modules`, each with the `.c` file compiled into
   `lib`, the content hashes of its files by kind (`module_file_kind`; 32 hexadecimal digits, empty if
   it has none) and `ModuleNativeData`; linked against the libraries of the manifests `deps`, whose
   modules have the `meta` symbols `extSymbols`.
   Returns, per module, why it found that its native code is not to be used, if it did. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_write_native_manifest(b_obj_arg oout, b_obj_arg olib, b_obj_arg odeps,
                                                                    b_obj_arg omodules, b_obj_arg oext) {
#ifdef PAPERLEAN_NATIVE_LIBS
    if (strlen(lean_string_cstr(oout)) + 1 != lean_string_size(oout)) return mk_embedded_nul_error(oout);
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
    std::vector<std::string> whys;
    std::vector<native_part> parts;
    // `NativeManifestModule`, `ModuleNativeData`
    auto symbols_of = [](object * p) { return lean_ctor_get(lean_ctor_get(p, 3), 0); };
    std::unordered_set<std::string> all;
    auto add_symbols = [&](object * a) {
        for (size_t j = 0; j < lean_array_size(a); j++) all.insert(lean_string_cstr(lean_array_get_core(a, j)));
    };
    add_symbols(oext);
    for (size_t i = 0; i < lean_array_size(omodules); i++) add_symbols(symbols_of(lean_array_get_core(omodules, i)));
    // Only the symbol set is shared between modules. Keep each unit's text alive through its
    // analysis (the tables contain string_views into it), then release it before reading the next.
    for (size_t i = 0; i < lean_array_size(omodules); i++) {
        object * p = lean_array_get_core(omodules, i);
        object * n = lean_ctor_get(p, 0);
        char const * cfile = lean_string_cstr(lean_ctor_get(p, 1));
        object * hashes = lean_ctor_get(p, 2);
        bool differs = lean_ctor_get_uint8(lean_ctor_get(p, 3), 4 * sizeof(void *));
        native_module m;
        memset(&m, 0, sizeof(m));
        c_unit u;
        if (!read_c_unit(cfile, u) || !c_init_flags(u, m.flags))
            return fail(std::string("cannot read the initializers of ") + cfile);
        if (meta_init_local(u)) m.flags |= native_meta_init_local;
        m.flags |= meta_code_flags(u, symbols_of(p), all);
        if (differs) m.flags |= native_differs;
        bool both_phases = (m.flags & native_runtime_init_runs) && (m.flags & native_meta_init_runs);
        whys.push_back(both_phases ? "it has `[init]` declarations of both phases, which its native initializers would run in another order" : "");
        // as the loader compares the imported modules' names
        m.name = add(name(n, true).to_string());
        m.name_hash = lean_name_hash(n);
        m.first_part = static_cast<uint32_t>(parts.size());
        if (lean_array_size(hashes) != num_module_file_kinds) return fail("expected a hash per kind of file");
        for (uint32_t kind = 0; kind < num_module_file_kinds; kind++) {
            char const * hex = lean_string_cstr(lean_array_get_core(hashes, kind));
            if (!*hex) continue;
            native_part part;
            memset(&part, 0, sizeof(part));
            part.kind = kind;
            unsigned long long lo, hi;
            int used = 0;
            if (strlen(hex) != 32 || sscanf(hex, "%16llx%16llx%n", &lo, &hi, &used) != 2 || used != 32)
                return fail(std::string("not a content hash: ") + hex);
            part.hash = content_hash { lo, hi };
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
    side_file_output output(out_path);
    if (!output.open(0666) || !output.write_bytes(&hdr, sizeof(hdr)) ||
        !output.write_bytes(body.data(), body.size()) || !output.publish())
        return fail("cannot write " + out_path);
    object * r = lean_mk_empty_array();
    for (std::string const & why : whys) r = lean_array_push(r, lean_mk_string(why.c_str()));
    return io_result_mk_ok(r);
#else
    (void)oout; (void)olib; (void)odeps; (void)omodules; (void)oext;
    return io_result_mk_error("writeNativeManifest: native libraries are supported only on Linux and macOS");
#endif
}
}
