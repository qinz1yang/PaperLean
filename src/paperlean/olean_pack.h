/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>
#include "runtime/compact.h"

namespace lean {
// A file served from an olean pack (`LEAN_OLEAN_PACK`).
struct pack_hit {
    char * begin;       // the region's copy of the file in the pack
    size_t size;
    size_t orig_base;   // the file's `base_addr`
    object * root;
};

// Whether the file `fname`, to be read with `deps` as the regions of the earlier parts of its
// module, is served from a pack.
bool find_in_packs(std::string const & fname, std::vector<region_view> const & deps, pack_hit & hit);
// Whether `addr` lies in a pack.
bool in_packs(void const * addr);

// The identity of a file, as packs record it: device, inode, size, modification and change times.
struct file_identity {
    uint64_t dev, ino, size;
    int64_t mtime_sec, mtime_nsec, ctime_sec, ctime_nsec;
    bool operator==(file_identity const & o) const {
        return dev == o.dev && ino == o.ino && size == o.size && mtime_sec == o.mtime_sec &&
            mtime_nsec == o.mtime_nsec && ctime_sec == o.ctime_sec && ctime_nsec == o.ctime_nsec;
    }
};
// The identity of the file at `path`.
bool stat_identity(char const * path, file_identity & id);
// The files of a module: `.olean`, `.olean.server`, `.olean.private`, `.ir.sig` and `.ir`.
enum module_file_kind : uint32_t { file_olean, file_olean_server, file_olean_private, file_ir_sig, file_ir, num_module_file_kinds };
// The kind of the file at `path` by its extension, or `num_module_file_kinds`.
uint32_t module_file_kind_of(std::string_view path);
// For native libraries (`native_libs.cpp`): if `data` is the root of a part of the packed module
// named `n`, so that an import got it from the pack, the files of the module that the pack recorded
// with their identities, by kind, provided none changed since packing and the pack can serve all
// files that an import may read. A module file must have both IR files packed: an import reads
// them from disk otherwise.
bool packed_module_files(b_obj_arg n, b_obj_arg data, std::vector<std::pair<uint32_t, file_identity>> & files);

// For import images (`import_state.cpp`), which describe the first pack: the entries arrays of
// extension `ext_name` of all parts of the first pack, the identity of the first pack, and a string
// that identifies an extension name.
void for_each_first_pack_ext_entries(b_obj_arg ext_name, std::function<void(object *)> const & f);
bool first_pack_identity(uint64_t & checksum, uint64_t & base, uint64_t & size);
void extension_name_key(b_obj_arg n, std::string & key);

// In `library/module.cpp`: the `.olean` format and regions.
size_t olean_header_size();
size_t olean_header_base_addr_offset();
// The header flags of this build.
uint8_t olean_header_flags();
// Whether `h` starts an `.olean` header with this build's marker and flags; its version and base address.
bool olean_header_info(char const * h, uint8_t & version, size_t & base_addr);
// Whether the `.olean` header `h` passes the githash check of `lean_compacted_region_read` (in builds
// with `CHECK_OLEAN_VERSION`; always otherwise).
bool olean_header_githash_ok(char const * h);
// A `CompactedRegion` object.
object * mk_olean_region(b_obj_arg ofname, object * root, char * buffer, size_t base_addr, size_t full_sz, bool is_mmap);
}
