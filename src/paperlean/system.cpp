/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <thread>
#if !defined(LEAN_WINDOWS)
#include <cerrno>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#if defined(__APPLE__)
#include <sys/acl.h>
#include <membership.h>
#endif
#include <signal.h>
#include <unistd.h>
#endif
#if !defined(LEAN_WINDOWS)
#include <sys/statvfs.h>
#endif
#if defined(__linux__)
#include <algorithm>
#include <climits>
#include <cstdint>
#include <utility>
#include <vector>
#include <sched.h>
#include <sys/resource.h>
#endif
#include "runtime/object.h"
#include "runtime/io.h"
#include "paperlean/side_file.h"
#include "paperlean/olean_pack.h"

// Small system functions for `Lean.PaperLean.System` and Lake's `paperlean` command.

namespace lean {
// The projection oracle can exit before elaboration drains its local IO streams.
extern "C" LEAN_EXPORT obj_res lean_paperlean_projection_oracle_log(b_obj_arg line) {
    std::fwrite(lean_string_cstr(line), 1, lean_string_size(line) - 1, stderr);
    std::fputc('\n', stderr);
    std::fflush(stderr);
    return lean_box(0);
}

/* version : Unit → String -- `g_paperlean_version` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_version(obj_arg) {
    return lean_mk_string(g_paperlean_version);
}

/* build : Unit → String -- `g_paperlean_build` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_build(obj_arg) {
    return lean_mk_string(g_paperlean_build);
}

/* setEnv (name : @& String) (value : @& Option String) : BaseIO Unit
   Sets the variable `name` of this process to `value`, or unsets it. */
extern "C" LEAN_EXPORT obj_res lean_paperlean_set_env(b_obj_arg name, b_obj_arg value) {
#if defined(LEAN_WINDOWS)
    _putenv_s(lean_string_cstr(name), lean_is_scalar(value) ? "" : lean_string_cstr(lean_ctor_get(value, 0)));
#else
    if (lean_is_scalar(value)) unsetenv(lean_string_cstr(name));
    else setenv(lean_string_cstr(name), lean_string_cstr(lean_ctor_get(value, 0)), 1);
#endif
    return lean_box(0);
}

/* processAlive (pid : UInt32) : BaseIO Bool -- whether a process with that id exists */
extern "C" LEAN_EXPORT uint8 lean_paperlean_process_alive(uint32_t pid) {
#if defined(LEAN_WINDOWS)
    (void)pid;
    return true;
#else
    return kill(static_cast<pid_t>(pid), 0) == 0 || errno == EPERM;
#endif
}

#if defined(__linux__)
// A small file's contents; empty if it cannot be read.
static std::string read_small_file(std::string const & path) {
    std::string text;
    FILE * f = std::fopen(path.c_str(), "re");
    if (!f) return text;
    char buf[4096];
    size_t n;
    while (text.size() < 65536 && (n = std::fread(buf, 1, sizeof(buf), f)) > 0) text.append(buf, n);
    std::fclose(f);
    return text;
}

// The directories of this process's cgroup and of each of its ancestors, whose limits the kernel
// all applies: in the cgroup v2 hierarchy (`second` true) and in the cgroup v1 hierarchy that has
// the controller `v1_controller`. `PAPERLEAN_TEST_CGROUP=<dir>` reads `<dir>/self` and `<dir>/fs`
// instead of `/proc/self/cgroup` and `/sys/fs/cgroup` (tests).
static std::vector<std::pair<std::string, bool>> cgroup_dirs(char const * v1_controller) {
    std::vector<std::pair<std::string, bool>> dirs;
    char const * test = getenv("PAPERLEAN_TEST_CGROUP");
    std::string self = read_small_file(test ? std::string(test) + "/self" : "/proc/self/cgroup");
    std::string fs = test ? std::string(test) + "/fs" : "/sys/fs/cgroup";
    size_t pos = 0;
    while (pos < self.size()) {
        size_t end = self.find('\n', pos);
        if (end == std::string::npos) end = self.size();
        std::string line = self.substr(pos, end - pos);
        pos = end + 1;
        // `<hierarchy id>:<controllers>:<path>`; v2 has no controllers
        size_t c1 = line.find(':');
        size_t c2 = c1 == std::string::npos ? c1 : line.find(':', c1 + 1);
        if (c2 == std::string::npos) continue;
        std::string controllers = line.substr(c1 + 1, c2 - c1 - 1);
        std::string path = line.substr(c2 + 1);
        if (path == "/") path.clear();
        std::vector<std::string> mounts;
        bool v2 = controllers.empty();
        if (v2) {
            mounts.push_back(fs);
        } else {
            bool has = false;
            for (size_t s = 0; s <= controllers.size();) {
                size_t e = controllers.find(',', s);
                if (e == std::string::npos) e = controllers.size();
                if (controllers.compare(s, e - s, v1_controller) == 0) has = true;
                s = e + 1;
            }
            if (!has) continue;
            // (mounted as the controller list, e.g. `cpu,cpuacct`, often with a link per controller)
            mounts.push_back(fs + "/" + controllers);
            mounts.push_back(fs + "/" + v1_controller);
        }
        while (true) {
            for (std::string const & m : mounts) dirs.push_back({ m + path, v2 });
            if (path.empty()) break;
            size_t slash = path.rfind('/');
            path.resize(slash == std::string::npos ? 0 : slash);
        }
    }
    return dirs;
}

// The bytes that this process's cgroups let it use, `UINT64_MAX` if they set no limit.
static uint64_t cgroup_memory_limit() {
    uint64_t limit = UINT64_MAX;
    for (auto const & d : cgroup_dirs("memory")) {
        std::string text = read_small_file(d.first + (d.second ? "/memory.max" : "/memory.limit_in_bytes"));
        char * end = nullptr;
        errno = 0;
        unsigned long long v = std::strtoull(text.c_str(), &end, 10);
        // (`max`, v2's "no limit", does not parse; v1's is a huge number)
        if (end != text.c_str() && errno == 0 && v > 0) limit = std::min<uint64_t>(limit, v);
    }
    return limit;
}

// The CPUs that this process's cgroups' CPU quotas let it keep busy (rounded up), `UINT_MAX` if
// they set no quota.
static unsigned cgroup_cpu_limit() {
    unsigned limit = UINT_MAX;
    for (auto const & d : cgroup_dirs("cpu")) {
        long long quota = -1, period = 0;
        if (d.second) {
            // `<quota> <period>`, or `max <period>`
            std::string text = read_small_file(d.first + "/cpu.max");
            if (std::sscanf(text.c_str(), "%lld %lld", &quota, &period) != 2) continue;
        } else {
            std::string q = read_small_file(d.first + "/cpu.cfs_quota_us");
            std::string p = read_small_file(d.first + "/cpu.cfs_period_us");
            if (std::sscanf(q.c_str(), "%lld", &quota) != 1 || std::sscanf(p.c_str(), "%lld", &period) != 1) continue;
        }
        if (quota > 0 && period > 0) {
            long long cpus = (quota + period - 1) / period;
            limit = std::min<unsigned>(limit, static_cast<unsigned>(std::min<long long>(std::max(cpus, 1LL), UINT_MAX)));
        }
    }
    return limit;
}
#endif

/* numCPUs : BaseIO Nat -- the number of hardware threads that this process may use */
extern "C" LEAN_EXPORT obj_res lean_paperlean_num_cpus(obj_arg) {
    unsigned n = std::thread::hardware_concurrency();
#if defined(__linux__)
    // (a process restricted to some CPUs, e.g. by a batch scheduler, `taskset` or a container, would
    // otherwise run a compiler process for each CPU of the machine on those)
    cpu_set_t set;
    CPU_ZERO(&set);
    if (sched_getaffinity(0, sizeof(set), &set) == 0 && CPU_COUNT(&set) > 0)
        n = static_cast<unsigned>(CPU_COUNT(&set));
    n = std::min(n ? n : 1u, cgroup_cpu_limit());
#endif
    return lean_box(n ? n : 1);
}

/* addressRangeFree (base size : USize) : BaseIO Bool -- whether nothing of this process is mapped in the
   `size` bytes at `base`, so that it could map them there now */
extern "C" LEAN_EXPORT uint8 lean_paperlean_address_range_free(size_t base, size_t size) {
#if defined(LEAN_WINDOWS)
    (void)base; (void)size;
    return true;
#else
    if (size == 0) return true;
    int flags = MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE
#ifdef MAP_FIXED_NOREPLACE
        | MAP_FIXED_NOREPLACE
#endif
        ;
    // (a probe, without memory and removed at once; without `MAP_FIXED_NOREPLACE` the address is a
    // hint, which the kernel follows only if the range is free)
    void * m = mmap(reinterpret_cast<void *>(base), size, PROT_NONE, flags, -1, 0);
    if (m == MAP_FAILED) return false;
    munmap(m, size);
    return m == reinterpret_cast<void *>(base);
#endif
}

/* wallSeconds : BaseIO Nat -- the seconds since the epoch */
extern "C" LEAN_EXPORT obj_res lean_paperlean_wall_seconds(obj_arg) {
    return lean_uint64_to_nat(static_cast<uint64_t>(time(nullptr)));
}

/* totalMemory : BaseIO Nat -- the bytes of memory that this process may use, 0 if unknown */
extern "C" LEAN_EXPORT obj_res lean_paperlean_total_memory(obj_arg) {
#if defined(LEAN_WINDOWS)
    return lean_box(0);
#else
    long pages = sysconf(_SC_PHYS_PAGES), size = sysconf(_SC_PAGE_SIZE);
    uint64_t bytes = pages > 0 && size > 0 ? static_cast<uint64_t>(pages) * size : 0;
#if defined(__linux__)
    // (a batch job's or a container's memory limit, which compiler processes sized for the
    // machine's memory would exceed)
    uint64_t limit = cgroup_memory_limit();
    if (limit != UINT64_MAX) bytes = bytes ? std::min(bytes, limit) : limit;
#endif
    return lean_uint64_to_nat(bytes);
#endif
}

// The automatic per-user cache can contain bytes copied from a private project. Keep
// its root private before any temporary or completed entry is written. Explicit shared
// cache directories do not call this helper.
extern "C" LEAN_EXPORT obj_res lean_paperlean_private_cache_root(b_obj_arg path) {
#if defined(LEAN_WINDOWS)
    (void)path;
    return io_result_mk_error("private cache directories are not supported on this platform");
#else
    char const * name = lean_string_cstr(path);
    auto error = [&]() {
        int e = errno;
        return io_result_mk_error((std::string("cannot protect default PaperLean cache '") + name +
                                  "': " + strerror(e)).c_str());
    };
    if (strlen(name) + 1 != lean_string_size(path)) { errno = EINVAL; return error(); }
#if defined(__APPLE__)
    uuid_t owner_uuid;
    bool owner_uuid_ready = false;
    uuid_t parent_owner_uuid;
    bool parent_owner_uuid_ready = false;
    // Resolve lazily: ordinary roots and parents have no extended ACL entries.
    auto owner_grant = [&](acl_entry_t entry, uid_t uid) -> int {
        auto & expected = uid == geteuid() ? owner_uuid : parent_owner_uuid;
        bool & ready = uid == geteuid() ? owner_uuid_ready : parent_owner_uuid_ready;
        if (!ready) {
            int e = mbr_uid_to_uuid(uid, expected);
            if (e != 0) { errno = e; return -1; }
            ready = true;
        }
        void * qualifier = acl_get_qualifier(entry);
        if (!qualifier) return -1;
        bool same = memcmp(qualifier, expected, sizeof(expected)) == 0;
        acl_free(qualifier);
        return same ? 1 : 0;
    };
#endif
    // Do not change the permissions of the user's home or system-cache directory.
    // A root in an immediately replaceable directory cannot protect future writes.
    auto safe_parent = [&](std::string const & child) {
        auto slash = child.find_last_of('/');
        std::string parent = slash == std::string::npos ? "." : slash == 0 ? "/" : child.substr(0, slash);
        struct stat st;
        if (stat(parent.c_str(), &st) != 0) return false;
        if (!S_ISDIR(st.st_mode) || (st.st_uid != geteuid() && st.st_uid != 0) ||
            ((st.st_mode & 0022) != 0 && (st.st_mode & S_ISVTX) == 0)) {
            errno = EACCES;
            return false;
        }
#if defined(__APPLE__)
        int parent_fd = open(parent.c_str(), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        if (parent_fd < 0) return false;
        struct stat opened;
        int parent_error = 0;
        if (fstat(parent_fd, &opened) != 0) parent_error = errno;
        else if (opened.st_dev != st.st_dev || opened.st_ino != st.st_ino ||
                 opened.st_uid != st.st_uid || opened.st_mode != st.st_mode) parent_error = EAGAIN;
        acl_t acl = parent_error ? nullptr : acl_get_fd_np(parent_fd, ACL_TYPE_EXTENDED);
        if (!parent_error && !acl && errno != ENOENT && errno != ENOTSUP) parent_error = errno;
        if (acl) {
            if (acl_valid(acl) != 0) parent_error = errno;
            for (int index = 0; !parent_error; ++index) {
                acl_entry_t entry;
                if (acl_get_entry(acl, index, &entry) != 0) {
                    if (errno != EINVAL) parent_error = errno;
                    break;
                }
                acl_tag_t tag;
                if (acl_get_tag_type(entry, &tag) != 0) { parent_error = errno; break; }
                if (tag == ACL_EXTENDED_DENY) continue;
                if (tag != ACL_EXTENDED_ALLOW) { parent_error = EINVAL; break; }
                acl_permset_mask_t permissions;
                if (acl_get_permset_mask_np(entry, &permissions) != 0) { parent_error = errno; break; }
                // Conservative: even if another ACE currently denies the grant, do not
                // depend on ACL ordering to exclude another principal's replacement rights.
                auto replacement = ACL_ADD_FILE | ACL_ADD_SUBDIRECTORY | ACL_DELETE_CHILD |
                                   ACL_WRITE_SECURITY | ACL_CHANGE_OWNER;
                if ((permissions & replacement) == 0) continue;
                int owner = owner_grant(entry, geteuid());
                // A root-owned parent is already controlled by UID0, whose grant is
                // not an additional untrusted replacement capability.
                if (owner == 0 && opened.st_uid != geteuid()) owner = owner_grant(entry, opened.st_uid);
                if (owner < 0) parent_error = errno;
                else if (!owner) parent_error = EACCES;
            }
            acl_free(acl);
        }
        close(parent_fd);
        if (parent_error) { errno = parent_error; return false; }
#endif
        return true;
    };
    if (!safe_parent(name)) return error();
    struct stat selected;
    if (lstat(name, &selected) != 0) {
        if (errno != ENOENT) return error();
        if (mkdir(name, 0700) != 0 && errno != EEXIST) return error();
        if (lstat(name, &selected) != 0) return error();
    }
    if (selected.st_uid != geteuid() || (!S_ISDIR(selected.st_mode) && !S_ISLNK(selected.st_mode))) {
        errno = EACCES;
        return error();
    }
    // An owner-controlled root alias is useful for relocating a large cache. Its target
    // must also be owned, and the alias must still select the opened directory.
    char * resolved = realpath(name, nullptr);
    if (!resolved) return error();
    std::string target(resolved);
    free(resolved);
    if (!safe_parent(target)) return error();
    int fd = open(target.c_str(), O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) return error();
    auto fail = [&]() {
        int e = errno;
        close(fd);
        errno = e;
        return error();
    };
    auto selected_now = [&]() {
        struct stat link, at_path, opened;
        if (lstat(name, &link) != 0 || stat(name, &at_path) != 0 || fstat(fd, &opened) != 0) return false;
        if (link.st_dev != selected.st_dev || link.st_ino != selected.st_ino ||
            link.st_uid != geteuid() || !S_ISDIR(opened.st_mode) || opened.st_uid != geteuid() ||
            at_path.st_dev != opened.st_dev || at_path.st_ino != opened.st_ino) {
            errno = EAGAIN;
            return false;
        }
        return true;
    };
    if (!selected_now()) return fail();
#if defined(__APPLE__)
    // Darwin allow ACLs can grant access despite mode0700. Remove non-owner grants
    // from this root, preserving owner-only grants and every deny entry.
    // Never replace the whole ACL with an empty one.
    acl_t acl = acl_get_fd_np(fd, ACL_TYPE_EXTENDED);
    if (!acl) {
        // An open directory with no extended ACL reports ENOENT on Darwin.
        if (errno != ENOTSUP && errno != ENOENT) return fail();
    } else {
        bool changed = false;
        int acl_error = 0;
        if (acl_valid(acl) != 0) acl_error = errno;
        for (int index = 0; !acl_error;) {
            acl_entry_t entry;
            if (acl_get_entry(acl, index, &entry) != 0) {
                if (errno != EINVAL) acl_error = errno;
                break;
            }
            acl_tag_t tag;
            if (acl_get_tag_type(entry, &tag) != 0) { acl_error = errno; break; }
            if (tag == ACL_EXTENDED_ALLOW) {
                int owner = owner_grant(entry, geteuid());
                if (owner < 0) { acl_error = errno; break; }
                if (owner) {
                    ++index;
                } else {
                    if (acl_delete_entry(acl, entry) != 0) { acl_error = errno; break; }
                    changed = true;
                }
            } else if (tag == ACL_EXTENDED_DENY) {
                ++index;
            } else {
                acl_error = EINVAL;
            }
        }
        if (!acl_error && changed && acl_set_fd_np(fd, acl, ACL_TYPE_EXTENDED) != 0) acl_error = errno;
        acl_free(acl);
        if (acl_error) { errno = acl_error; return fail(); }
    }
#endif
    struct stat permissions;
    if (fstat(fd, &permissions) != 0) return fail();
    // Existing private roots need no metadata write, including on read-only or
    // mode-restricted paths. Keep their ctime unchanged when protection is a no-op.
    if ((permissions.st_mode & 0777) != 0700 && fchmod(fd, 0700) != 0) return fail();
    if (!selected_now()) return fail();
    struct stat done;
    if (fstat(fd, &done) != 0) return fail();
    if ((done.st_mode & 0777) != 0700) { errno = EACCES; return fail(); }
    if (close(fd) != 0) return error();
    return io_result_mk_ok(lean_box(0));
#endif
}

/* fileIdentity (path : @& String) : BaseIO (Option ByteArray) -- the identity of the file at `path`
   (`stat_identity`): a device field that is always 0 (host-independent, see `file_identity`), inode, size,
   and seconds and nanoseconds of the modification and status change times, as 7 64-bit integers in the
   machine's byte order; `none` if it has none */
extern "C" LEAN_EXPORT obj_res lean_paperlean_file_identity(b_obj_arg path) {
    file_identity id;
    if (!stat_identity(lean_string_cstr(path), id)) return lean_box(0);
    uint64_t v[7] = { id.dev, id.ino, id.size, static_cast<uint64_t>(id.mtime_sec),
                      static_cast<uint64_t>(id.mtime_nsec), static_cast<uint64_t>(id.ctime_sec),
                      static_cast<uint64_t>(id.ctime_nsec) };
    obj_res a = lean_alloc_sarray(1, sizeof(v), sizeof(v));
    memcpy(lean_sarray_cptr(a), v, sizeof(v));
    obj_res r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, a);
    return r;
}

/* limitAddressSpace (extra : USize) : BaseIO Unit
   Limits the address space of this process to what it holds now and `extra` bytes more, or lifts that
   limit if `extra` is 0: allocations beyond it fail. On Linux; elsewhere it does nothing (`RLIMIT_AS` is
   not enforced on macOS). */
extern "C" LEAN_EXPORT obj_res lean_paperlean_limit_address_space(size_t extra) {
#if defined(__linux__)
    struct rlimit limit;
    if (getrlimit(RLIMIT_AS, &limit) != 0) return lean_box(0);
    limit.rlim_cur = limit.rlim_max;
    if (extra) {
        unsigned long pages = 0;
        if (FILE * f = fopen("/proc/self/statm", "r")) {
            if (fscanf(f, "%lu", &pages) != 1) pages = 0;
            fclose(f);
        }
        if (pages) limit.rlim_cur = std::min<rlim_t>(limit.rlim_max, pages * sysconf(_SC_PAGE_SIZE) + extra);
    }
    setrlimit(RLIMIT_AS, &limit);
#else
    (void)extra;
#endif
    return lean_box(0);
}

/* freeSpace (path : @& String) : IO Nat -- bytes available to this user on the file system of `path` */
extern "C" LEAN_EXPORT obj_res lean_paperlean_free_space(b_obj_arg path) {
#if defined(LEAN_WINDOWS)
    (void)path;
    return io_result_mk_error("freeSpace: not supported on Windows");
#else
    struct statvfs st;
    if (statvfs(lean_string_cstr(path), &st) != 0)
        return io_result_mk_error((std::string("freeSpace: cannot read ") + lean_string_cstr(path)).c_str());
    return io_result_mk_ok(lean_uint64_to_nat(static_cast<uint64_t>(st.f_bavail) * st.f_frsize));
#endif
}
}
