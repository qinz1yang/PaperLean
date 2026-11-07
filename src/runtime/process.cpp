/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
// The inherited-handle list is available in Windows Vista and later.
#if defined(LEAN_WINDOWS) && !defined(_WIN32_WINNT)
#define _WIN32_WINNT 0x0600
#endif
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include <memory>
#include <system_error>

#if defined(LEAN_WINDOWS)
#include "runtime/windows_argv.h"
#include <climits>
#include <cstring>
#include <cwchar>
#include <map>
#include <new>
#include <stdexcept>
#include <type_traits>
#include <vector>
#include <windows.h>
#include <fcntl.h>
#include <io.h>
#include <tchar.h>
#include <stdio.h>
#include <strsafe.h>
#else
#include <algorithm>
#include <cstring>
#include <vector>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <signal.h>
#include <limits.h> // NOLINT
#ifdef __APPLE__
#include <mutex>
#include <crt_externs.h>
#include <paths.h>
#include <sys/stat.h>
#endif
#endif

#ifdef __linux
#include <sys/syscall.h>
#endif

#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/array_ref.h"
#include "runtime/string_ref.h"
#include "runtime/option_ref.h"
#include "runtime/pair_ref.h"
#include "runtime/buffer.h"

namespace lean {

enum stdio {
    PIPED,
    INHERIT,
    NUL,
};

#if defined(LEAN_WINDOWS)

static lean_external_class * g_win_handle_external_class = nullptr;

static void win_handle_finalizer(void * h) {
    lean_always_assert(CloseHandle(static_cast<HANDLE>(h)));
}

static void win_handle_foreach(void * /* mod */, b_obj_arg /* fn */) {
}

lean_object * wrap_win_handle(HANDLE h) {
    return lean_alloc_external(g_win_handle_external_class, static_cast<void *>(h));
}

static std::system_error win_error(DWORD code) {
    return std::system_error(static_cast<int>(code), std::system_category());
}

// Lean strings are UTF-8. Win32 takes NUL-terminated UTF-16 strings.
static std::wstring win_string(string_ref const & s) {
    size_t bytes = s.num_bytes();
    if (bytes == 0) return {};
    if (bytes > INT_MAX || std::memchr(s.data(), '\0', bytes)) throw win_error(ERROR_INVALID_PARAMETER);
    int n = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, s.data(), static_cast<int>(bytes), nullptr, 0);
    if (n == 0) throw win_error(GetLastError());
    std::wstring result(n, L'\0');
    int written = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, s.data(), static_cast<int>(bytes), result.data(), n);
    if (written != n) throw win_error(written ? ERROR_INVALID_DATA : GetLastError());
    return result;
}

// Match the previous Win32 cwd error convention and contain C++ failures at the FFI boundary.
template<class Action>
static obj_res win_cwd_result(Action action) {
    try {
        return action();
    } catch (std::system_error const & err) {
        return io_result_mk_error((sstream() << err.code().value()).str());
    } catch (std::bad_alloc const &) {
        return io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    } catch (std::length_error const &) {
        return io_result_mk_error(decode_io_error(E2BIG, nullptr));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_get_current_dir() {
    return win_cwd_result([]() -> obj_res {
        DWORD capacity = GetCurrentDirectoryW(0, nullptr);
        if (!capacity) throw win_error(GetLastError());
        for (;;) {
            if (capacity > INT_MAX) throw win_error(ERROR_FILENAME_EXCED_RANGE);
            std::wstring path(capacity, L'\0');
            DWORD length = GetCurrentDirectoryW(capacity, path.data());
            if (!length) throw win_error(GetLastError());
            // On insufficient space Windows returns the required capacity, including NUL.
            // A concurrent SetCurrentDirectoryW can change the size between the two calls.
            if (length >= capacity) {
                capacity = length == capacity ? capacity + 1 : length;
                continue;
            }
            int units = static_cast<int>(length);
            int bytes = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, path.data(), units, nullptr, 0, nullptr, nullptr);
            if (!bytes) throw win_error(GetLastError());
            std::string utf8(bytes, '\0');
            int written = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, path.data(), units,
                                              utf8.data(), bytes, nullptr, nullptr);
            if (written != bytes) throw win_error(written ? ERROR_INVALID_DATA : GetLastError());
            return io_result_mk_ok(lean_mk_string_from_bytes(utf8.data(), utf8.size()));
        }
    });
}

extern "C" LEAN_EXPORT obj_res lean_io_process_set_current_dir(b_obj_arg path) {
    return win_cwd_result([&]() -> obj_res {
        std::wstring wide = win_string(string_ref(path, true));
        if (!SetCurrentDirectoryW(wide.c_str())) throw win_error(GetLastError());
        return io_result_mk_ok(box(0));
    });
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_get_pid() {
    return GetCurrentProcessId();
}

extern "C" LEAN_EXPORT uint64_t lean_io_get_tid() {
    return GetCurrentThreadId();
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    DWORD exit_code;
    if (WaitForSingleObject(h, INFINITE) == WAIT_FAILED) {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
    if (!GetExitCodeProcess(h, &exit_code)) {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
    return lean_io_result_mk_ok(box_uint32(exit_code));
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    DWORD exit_code;
    DWORD ret = WaitForSingleObject(h, 0);
    if (ret == WAIT_FAILED) {
        return io_result_mk_error((sstream() << GetLastError()).str());
    } else if (ret == WAIT_TIMEOUT) {
        return io_result_mk_ok(mk_option_none());
    } else {
        if (!GetExitCodeProcess(h, &exit_code)) {
            return io_result_mk_error((sstream() << GetLastError()).str());
        }
        return lean_io_result_mk_ok(mk_option_some(box_uint32(exit_code)));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    if (!TerminateProcess(h, 1)) {
        return io_result_mk_error((sstream() << GetLastError()).str());
    }
    return lean_io_result_mk_ok(box(0));
}

// Output has one consuming owner. Observation must leave the process identity
// reserved until the owner has decided between ordinary completion and cancellation.
extern "C" LEAN_EXPORT obj_res lean_io_process_output_observe(b_obj_arg, b_obj_arg child, uint8_t block) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    DWORD result = WaitForSingleObject(h, block ? INFINITE : 0);
    if (result == WAIT_OBJECT_0 || result == WAIT_TIMEOUT)
        return io_result_mk_ok(box(result == WAIT_OBJECT_0));
    return io_result_mk_error((sstream() << GetLastError()).str());
}

extern "C" LEAN_EXPORT obj_res lean_io_process_output_reap(b_obj_arg cfg, b_obj_arg child) {
    return lean_io_process_child_wait(cfg, child);
}

extern "C" LEAN_EXPORT obj_res lean_io_process_output_kill(b_obj_arg cfg, b_obj_arg child) {
    return lean_io_process_child_kill(cfg, child);
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
    HANDLE h = static_cast<HANDLE>(lean_get_external_data(cnstr_get(child, 3)));
    return GetProcessId(h);
}

class scoped_win_handle {
    HANDLE m_handle;
public:
    explicit scoped_win_handle(HANDLE handle = INVALID_HANDLE_VALUE): m_handle(handle) {}
    scoped_win_handle(scoped_win_handle const &) = delete;
    scoped_win_handle & operator=(scoped_win_handle const &) = delete;
    ~scoped_win_handle() { reset(); }
    HANDLE get() const { return m_handle; }
    HANDLE release() { return std::exchange(m_handle, INVALID_HANDLE_VALUE); }
    void reset(HANDLE handle = INVALID_HANDLE_VALUE) {
        if (m_handle != INVALID_HANDLE_VALUE && m_handle != NULL) CloseHandle(m_handle);
        m_handle = handle;
    }
};

static object_ref from_win_handle(scoped_win_handle & handle, char const * mode) {
    int fd = _open_osfhandle(reinterpret_cast<intptr_t>(handle.get()), _O_APPEND);
    if (fd == -1) throw errno;
    // The CRT descriptor now owns the native handle.
    handle.release();
    FILE * file = fdopen(fd, mode);
    if (file == nullptr) {
        int err = errno;
        _close(fd);
        throw err;
    }
    std::unique_ptr<FILE, decltype(&fclose)> owner(file, fclose);
    object_ref result(io_wrap_handle(file));
    owner.release();
    return result;
}

static void setup_stdio(SECURITY_ATTRIBUTES * saAttr, DWORD std_handle,
                        scoped_win_handle & theirs, object_ref & ours, bool in, stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT: {
        // GUI/service parents may legitimately have no standard handle. A failed
        // lookup or duplication is different and must still fail this spawn.
        SetLastError(ERROR_SUCCESS);
        HANDLE inherited = GetStdHandle(std_handle);
        if (inherited == INVALID_HANDLE_VALUE) {
            DWORD error = GetLastError();
            throw win_error(error ? error : ERROR_INVALID_HANDLE);
        }
        if (inherited == nullptr) {
            theirs.reset(nullptr);
            return;
        }
        HANDLE duplicate;
        if (!DuplicateHandle(GetCurrentProcess(), inherited, GetCurrentProcess(), &duplicate,
                             0, TRUE, DUPLICATE_SAME_ACCESS))
            throw std::system_error(GetLastError(), std::system_category());
        theirs.reset(duplicate);
        return;
    }
    case stdio::PIPED: {
        HANDLE readh;
        HANDLE writeh;
        if (!CreatePipe(&readh, &writeh, saAttr, 0))
            throw std::system_error(GetLastError(), std::system_category());
        scoped_win_handle parent(in ? writeh : readh);
        theirs.reset(in ? readh : writeh);
        // Only the child's endpoint may be inherited.
        if (!SetHandleInformation(parent.get(), HANDLE_FLAG_INHERIT, 0))
            throw std::system_error(GetLastError(), std::system_category());
        ours = from_win_handle(parent, in ? "w" : "r");
        return;
    }
    case stdio::NUL: {
        HANDLE hNul = CreateFileW(L"NUL",
                                 in ? GENERIC_READ : GENERIC_WRITE,
                                 FILE_SHARE_READ | FILE_SHARE_WRITE,
                                 saAttr,
                                 OPEN_EXISTING,
                                 FILE_ATTRIBUTE_NORMAL,
                                 NULL);
        if (hNul == INVALID_HANDLE_VALUE)
            throw std::system_error(GetLastError(), std::system_category());
        theirs.reset(hNul);
        return;
    }
    }
    lean_unreachable();
}

struct win_env_less {
    bool operator()(std::wstring const & a, std::wstring const & b) const {
        int result = CompareStringOrdinal(a.c_str(), -1, b.c_str(), -1, TRUE);
        if (!result) throw win_error(GetLastError());
        return result == CSTR_LESS_THAN;
    }
};

static std::vector<wchar_t> win_environment(array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & updates,
                                            bool inherit) {
    // A null lpEnvironment asks Windows to copy the entire parent environment.
    if (inherit && updates.size() == 0) return {};
    std::map<std::wstring, std::wstring, win_env_less> vars;
    if (inherit) {
        std::unique_ptr<wchar_t, decltype(&FreeEnvironmentStringsW)> block(GetEnvironmentStringsW(), FreeEnvironmentStringsW);
        if (!block) throw win_error(GetLastError());
        for (wchar_t const * p = block.get(); *p; p += std::wcslen(p) + 1) {
            // Hidden per-drive entries are shaped like '=C:=C:\\dir'.
            wchar_t const * sep = std::wcschr(p + 1, L'=');
            if (!sep) throw win_error(ERROR_BAD_ENVIRONMENT);
            vars[std::wstring(p, sep)] = sep + 1;
        }
    }
    for (auto const & entry : updates) {
        std::wstring key = win_string(entry.fst());
        if (key.empty() || key.find(L'=') != std::wstring::npos) throw win_error(ERROR_INVALID_PARAMETER);
        auto value = entry.snd();
        if (value) vars[key] = win_string(*value.get());
        else vars.erase(key);
    }
    std::vector<wchar_t> block;
    for (auto const & kv : vars) {
        block.insert(block.end(), kv.first.begin(), kv.first.end());
        block.push_back(L'=');
        block.insert(block.end(), kv.second.begin(), kv.second.end());
        block.push_back(L'\0');
    }
    if (block.empty()) block.push_back(L'\0');
    block.push_back(L'\0');
    return block;
}

static PROCESS_INFORMATION create_child(std::wstring & command, wchar_t const * cwd,
                                        std::vector<wchar_t> & environment, HANDLE (&handles)[3]) {
    HANDLE inherited[3];
    size_t count = 0;
    for (HANDLE h : handles) {
        if (h == INVALID_HANDLE_VALUE) throw win_error(ERROR_INVALID_HANDLE);
        if (h) inherited[count++] = h;
    }
    STARTUPINFOEXW startup{};
    startup.StartupInfo.cb = sizeof(STARTUPINFOW);
    startup.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
    startup.StartupInfo.hStdInput = handles[0];
    startup.StartupInfo.hStdOutput = handles[1];
    startup.StartupInfo.hStdError = handles[2];
    DWORD flags = CREATE_UNICODE_ENVIRONMENT;
    std::unique_ptr<unsigned char[]> storage;
    std::unique_ptr<std::remove_pointer_t<LPPROC_THREAD_ATTRIBUTE_LIST>, decltype(&DeleteProcThreadAttributeList)>
        initialized(nullptr, DeleteProcThreadAttributeList);
    if (count) {
        SIZE_T bytes = 0;
        if (InitializeProcThreadAttributeList(nullptr, 1, 0, &bytes)) throw win_error(ERROR_INVALID_DATA);
        DWORD error = GetLastError();
        if (error != ERROR_INSUFFICIENT_BUFFER) throw win_error(error);
        storage = std::make_unique<unsigned char[]>(bytes);
        auto list = reinterpret_cast<LPPROC_THREAD_ATTRIBUTE_LIST>(storage.get());
        if (!InitializeProcThreadAttributeList(list, 1, 0, &bytes)) throw win_error(GetLastError());
        initialized.reset(list);
        if (!UpdateProcThreadAttribute(list, 0, PROC_THREAD_ATTRIBUTE_HANDLE_LIST, inherited,
                                       count * sizeof(HANDLE), nullptr, nullptr)) throw win_error(GetLastError());
        startup.lpAttributeList = list;
        startup.StartupInfo.cb = sizeof(startup);
        flags |= EXTENDED_STARTUPINFO_PRESENT;
    }
    PROCESS_INFORMATION info{};
    // Keep lpApplicationName null to preserve PATH search and implicit .exe handling.
    if (!CreateProcessW(nullptr, command.data(), nullptr, nullptr, count ? TRUE : FALSE, flags,
                        environment.empty() ? nullptr : environment.data(), cwd, &startup.StartupInfo, &info))
        throw win_error(GetLastError());
    return info;
}

static obj_res spawn(string_ref const & proc_name, array_ref<string_ref> const & args, stdio stdin_mode, stdio stdout_mode,
                     stdio stderr_mode, option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env,
                     bool inherit_env, bool _do_setsid) {
    std::wstring program = win_string(proc_name);
    if (program.empty() || program.find(L'"') != std::wstring::npos) throw win_error(ERROR_INVALID_PARAMETER);
    // argv[0] is a quoted executable pathname, not a normal CRT argument.
    std::wstring command = L"\"" + program + L"\"";
    if (command.size() >= 32767) throw win_error(ERROR_FILENAME_EXCED_RANGE);
    for (auto const & arg : args) {
        append_windows_arg(command, win_string(arg));
        if (command.size() >= 32767) throw win_error(ERROR_FILENAME_EXCED_RANGE);
    }
    auto environment = win_environment(env, inherit_env);
    std::wstring directory = cwd ? win_string(*cwd.get()) : std::wstring();

    scoped_win_handle child_stdin, child_stdout, child_stderr;
    object_ref parent_stdin, parent_stdout, parent_stderr;
    SECURITY_ATTRIBUTES sa{sizeof(sa), nullptr, TRUE};
    setup_stdio(&sa, STD_INPUT_HANDLE, child_stdin, parent_stdin, true, stdin_mode);
    setup_stdio(&sa, STD_OUTPUT_HANDLE, child_stdout, parent_stdout, false, stdout_mode);
    setup_stdio(&sa, STD_ERROR_HANDLE, child_stderr, parent_stderr, false, stderr_mode);
    HANDLE handles[] = {child_stdin.get(), child_stdout.get(), child_stderr.get()};
    PROCESS_INFORMATION piProcInfo = create_child(command, cwd ? directory.c_str() : nullptr, environment, handles);

    scoped_win_handle process(piProcInfo.hProcess);
    scoped_win_handle thread(piProcInfo.hThread);
    // All child-side handles belong to this spawn, including inherited duplicates and NUL.
    child_stdin.reset();
    child_stdout.reset();
    child_stderr.reset();

    object_ref process_object(wrap_win_handle(process.get()));
    process.release();
    object_ref r = mk_cnstr(0, parent_stdin, parent_stdout, parent_stderr, process_object);
    return lean_io_result_mk_ok(r.steal());
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg lchild) {
    object_ref child(lchild);
    object_ref child2 = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1), cnstr_get_ref(child, 2), cnstr_get_ref(child, 3));
    object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), child2);
    return lean_io_result_mk_ok(r.steal());
}

void initialize_process() {
    g_win_handle_external_class = lean_register_external_class(win_handle_finalizer, win_handle_foreach);
}
void finalize_process() {}

#else

extern "C" LEAN_EXPORT obj_res lean_io_process_get_current_dir() {
    char path[PATH_MAX];
    if (getcwd(path, PATH_MAX)) {
        return io_result_mk_ok(mk_string(path));
    } else {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_set_current_dir(b_obj_arg path) {
    if (!chdir(string_cstr(path))) {
        return io_result_mk_ok(box(0));
    } else {
        return io_result_mk_error(decode_io_error(errno, path));
    }
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_get_pid() {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    return getpid();
}

extern "C" LEAN_EXPORT uint64_t lean_io_get_tid() {
    uint64_t tid;
#ifdef __APPLE__
    lean_always_assert(pthread_threadid_np(NULL, &tid) == 0);
#elif defined(LEAN_EMSCRIPTEN)
    tid = 0;
#else
    // since Linux 2.4.11, our glibc 2.27 requires at least 3.2
    // glibc 2.30 would provide a wrapper
    tid = (pid_t)syscall(SYS_gettid);
#endif
    return tid;
}

static obj_res wait_child(b_obj_arg child, bool retry_interrupt) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    int status;
    pid_t result;
    do { result = waitpid(pid, &status, 0); } while (result == -1 && retry_interrupt && errno == EINTR);
    if (result == -1) {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
    if (WIFEXITED(status)) {
        return lean_io_result_mk_ok(box_uint32(static_cast<unsigned>(WEXITSTATUS(status))));
    } else {
        lean_assert(WIFSIGNALED(status));
        // use bash's convention
        return lean_io_result_mk_ok(box_uint32(128 + static_cast<unsigned>(WTERMSIG(status))));
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_wait(b_obj_arg, b_obj_arg child) {
    return wait_child(child, false);
}

extern "C" LEAN_EXPORT obj_res lean_io_process_output_reap(b_obj_arg, b_obj_arg child) {
    return wait_child(child, true);
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_try_wait(b_obj_arg, b_obj_arg child) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    int status;
    int ret = waitpid(pid, &status, WNOHANG);
    if (ret == -1) {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    } else if (ret == 0) {
        return io_result_mk_ok(mk_option_none());
    } else {
        if (WIFEXITED(status)) {
            obj_res output = box_uint32(static_cast<unsigned>(WEXITSTATUS(status)));
            return lean_io_result_mk_ok(mk_option_some(output));
        } else {
            lean_assert(WIFSIGNALED(status));
            // use bash's convention
            obj_res output = box_uint32(128 + static_cast<unsigned>(WTERMSIG(status)));
            return lean_io_result_mk_ok(mk_option_some(output));
        }
    }
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_kill(b_obj_arg, b_obj_arg child) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    bool setsid = cnstr_get_uint8(child, 3 * sizeof(object *) + sizeof(pid_t));
    if ((setsid ? killpg(pid, SIGKILL) : kill(pid, SIGKILL)) == -1) {
        return io_result_mk_error(decode_io_error(errno, nullptr));
    }
    return lean_io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_io_process_output_observe(b_obj_arg, b_obj_arg child, uint8_t block) {
#if defined(WNOWAIT)
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    siginfo_t info{};
    int result;
    do {
        result = waitid(P_PID, static_cast<id_t>(pid), &info, WEXITED | WNOWAIT | (block ? 0 : WNOHANG));
    } while (result == -1 && errno == EINTR);
    if (result == -1) return io_result_mk_error(decode_io_error(errno, nullptr));
    return io_result_mk_ok(box(info.si_pid != 0));
#else
    // The Emscripten runtime does not support spawning POSIX child processes.
    return io_result_mk_error(decode_io_error(ENOSYS, nullptr));
#endif
}

extern "C" LEAN_EXPORT obj_res lean_io_process_output_kill(b_obj_arg, b_obj_arg child) {
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    bool session = cnstr_get_uint8(child, 3 * sizeof(object *) + sizeof(pid_t));
    if (session) {
        if (killpg(pid, SIGKILL) == 0) return io_result_mk_ok(box(0));
        if (errno != ESRCH) return io_result_mk_error(decode_io_error(errno, nullptr));
    }
    // The owner has not reaped this PID. If cancellation arrived before its setsid(),
    // kill it directly, then catch the group if setsid raced the first signal.
    if (kill(pid, SIGKILL) == -1) return io_result_mk_error(decode_io_error(errno, nullptr));
    if (session) (void)killpg(pid, SIGKILL);
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT uint32_t lean_io_process_child_pid(b_obj_arg, b_obj_arg child) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    return pid;
}

struct pipe {
    int m_read_fd;
    int m_write_fd;
    pipe(int read_fd, int write_fd): m_read_fd(read_fd), m_write_fd(write_fd) {}
    pipe(pipe const &) = delete;
    pipe & operator=(pipe const &) = delete;
    pipe(pipe && other) noexcept:
        m_read_fd(other.release_read()), m_write_fd(other.release_write()) {}
    ~pipe() {
        close_read();
        close_write();
    }
    int release_read() { return std::exchange(m_read_fd, -1); }
    int release_write() { return std::exchange(m_write_fd, -1); }
    void close_read() { if (m_read_fd != -1) close(release_read()); }
    void close_write() { if (m_write_fd != -1) close(release_write()); }
};

// Own every copied argument before another allocation can fail. This owner is destroyed only
// in the parent: the child either replaces its image with execve or terminates with _exit.
class process_args {
    buffer<char *> m_args;
public:
    process_args() = default;
    process_args(process_args const &) = delete;
    process_args & operator=(process_args const &) = delete;
    ~process_args() { for (char * arg : m_args) free(arg); }
    void push(char const * arg) {
        std::unique_ptr<char, decltype(&free)> copy(strdup(arg), free);
        if (!copy) throw ENOMEM;
        m_args.push_back(copy.get());
        copy.release();
    }
    void finish() { m_args.push_back(nullptr); }
    char * operator[](size_t i) const { return m_args[i]; }
    char ** data() { return m_args.data(); }
};

static object_ref parent_pipe_handle(pipe & p, bool input) {
    int fd = input ? p.m_write_fd : p.m_read_fd;
    FILE * file = fdopen(fd, input ? "w" : "r");
    if (file == nullptr) throw errno;
    if (input) p.release_write(); else p.release_read();
    std::unique_ptr<FILE, decltype(&fclose)> owner(file, fclose);
    object_ref result(io_wrap_handle(file));
    owner.release();
    return result;
}

// A pipe acquired when stdin/stdout/stderr is closed can overlap a later dup2 target.
// Keep both endpoints above the standard descriptors, including the parent's FILE handle.
static void move_pipe_fd(int & fd) {
    if (fd > STDERR_FILENO) return;
    int high = fcntl(fd, F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
    if (high < 0) throw errno;
    close(std::exchange(fd, high));
}

#ifdef __APPLE__
// Darwin has no pipe2(O_CLOEXEC). A concurrent Lean spawn must not fork
// between pipe() and setting FD_CLOEXEC on both ends.
static std::mutex g_spawn_fd_mutex;
static pid_t fork_process() {
    std::unique_lock<std::mutex> lock(g_spawn_fd_mutex);
    pid_t pid = fork();
    if (pid == 0) {
        lock.release();  // The child only redirects and execs or _exits.
    } else {
        int err = errno;
        lock.unlock();
        if (pid < 0) errno = err;
    }
    return pid;
}
#else
static pid_t fork_process() { return fork(); }
#endif

static optional<pipe> setup_stdio(stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        /* We should need to do nothing in this case */
        return optional<pipe>();
    case stdio::PIPED: {
        int fds[2];
#ifdef __APPLE__
        std::lock_guard<std::mutex> lock(g_spawn_fd_mutex);
        if (::pipe(fds) == -1) { throw errno; }
        optional<pipe> result(std::in_place, fds[0], fds[1]);
        if (::fcntl(fds[0], F_SETFD, FD_CLOEXEC)) { throw errno; }
        if (::fcntl(fds[1], F_SETFD, FD_CLOEXEC)) { throw errno; }
#else
        if (::pipe2(fds, O_CLOEXEC) == -1) { throw errno; }
        optional<pipe> result(std::in_place, fds[0], fds[1]);
#endif
        move_pipe_fd(result->m_read_fd);
        move_pipe_fd(result->m_write_fd);
        return result;
    }
    case stdio::NUL:
        /* We should map /dev/null. */
        return optional<pipe>();
    }
    lean_unreachable();
}

// Prepare environment edits and diagnostics before fork.
static char *** process_environ_slot() {
#ifdef __APPLE__
    return _NSGetEnviron();
#else
    return &environ;
#endif
}

#if defined(__APPLE__) || defined(__GLIBC__)
static std::string default_exec_path() {
#ifdef __APPLE__
    return _PATH_DEFPATH;
#else
    size_t n = confstr(_CS_PATH, nullptr, 0);
    if (n) {
        std::vector<char> path(n);
        if (confstr(_CS_PATH, path.data(), n) == n) return path.data();
    }
    return "/bin:/usr/bin";
#endif
}

#endif

struct child_environment {
    std::vector<std::string> entries;
    std::vector<char *> pointers;
    child_environment(bool inherit, char ** inherited,
                      array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & changes) {
        // For unmodified inheritance, let the child read the actual fork-time environ.
        // A borrowed environ array captured earlier could be invalidated by a later setenv.
        if (inherit && changes.size() == 0) return;
        if (inherit && inherited) {
            for (char ** p = inherited; *p; ++p) entries.emplace_back(*p);
        }
        for (auto & change : changes) {
            std::string key(change.fst().data());
            // setenv/unsetenv reject these names. The previous implementation ignored that error.
            if (key.empty() || key.find('=') != std::string::npos) continue;
            key += '=';
            auto matches = [&](std::string const & e) { return e.compare(0, key.size(), key) == 0; };
            if (change.snd()) {
                std::string value = key + change.snd().get()->data();
                auto it = std::find_if(entries.begin(), entries.end(), matches);
                if (it == entries.end()) entries.push_back(std::move(value));
                else *it = std::move(value);
            } else {
                entries.erase(std::remove_if(entries.begin(), entries.end(), matches), entries.end());
            }
        }
        for (auto & e : entries) pointers.push_back(e.data());
        pointers.push_back(nullptr);
    }
};

static void child_write(char const * text, size_t n) {
    while (n) {
        ssize_t r = write(STDERR_FILENO, text, n);
        if (r < 0 && errno == EINTR) continue;
        if (r <= 0) return;
        text += r;
        n -= static_cast<size_t>(r);
    }
}

[[noreturn]] static void child_fail(char const * msg, size_t n) {
    child_write(msg, n);
    _exit(255);  // Do not flush any FILE buffers inherited from the parent.
}

static constexpr int inherit_stdio = -1;
static constexpr int null_stdio = -2;

static bool child_redirect(int source, int target) {
    if (source == inherit_stdio) return true;
    if (source == null_stdio) {
        int flags = (target == STDIN_FILENO ? O_RDONLY : O_WRONLY) | O_CLOEXEC;
        do { source = open("/dev/null", flags); } while (source < 0 && errno == EINTR);
        if (source < 0) return false;
    }
    if (source == target) {
        // open can itself return a closed standard descriptor. dup2(fd, fd) would
        // leave FD_CLOEXEC set, causing the child to lose this stream at exec.
        int r;
        do { r = fcntl(source, F_SETFD, 0); } while (r < 0 && errno == EINTR);
        return r >= 0;
    }
    int r;
    do { r = dup2(source, target); } while (r < 0 && errno == EINTR);
    close(source);  // All sources also have FD_CLOEXEC.
    return r >= 0;
}

#if defined(__APPLE__) || defined(__GLIBC__)
// Continue searching after a missing/non-executable PATH entry. macOS also
// distinguishes failures of stat on the candidate from errors on an existing file.
static bool child_search_next(char const * candidate, int err) {
    if (err == EACCES || err == ENOENT || err == ENOTDIR) return true;
#ifdef __APPLE__
    if (err == ELOOP || err == ENAMETOOLONG) return true;
    if (err == E2BIG || err == ENOMEM || err == ETXTBSY) return false;
    struct stat st;
    return stat(candidate, &st) != 0;
#else
    (void)candidate;
    return err == ESTALE || err == ENODEV || err == ETIMEDOUT;
#endif
}

static int child_exec_one(char const * file, char * const * argv, char ** sh_argv, char ** envp) {
    execve(file, argv, envp);
    if (errno == ENOEXEC) {
        sh_argv[1] = const_cast<char *>(file);
        execve("/bin/sh", sh_argv, envp);
#ifdef __APPLE__
        return 0;  // The shell fallback is terminal on Darwin, including failure.
#endif
    }
    return errno;
}

static void child_exec(char * const * argv, char ** sh_argv, char ** envp, char const * path) {
    char const * name = argv[0];
    if (!*name) return;
    if (strchr(name, '/')) {
        child_exec_one(name, argv, sh_argv, envp);
        return;
    }
    size_t name_len = strlen(name);
#ifdef __GLIBC__
    if (name_len > NAME_MAX) return;
#endif
    char file[PATH_MAX];
    while (true) {
        char const * end = strchr(path, ':');
        size_t dir_len = end ? static_cast<size_t>(end - path) : strlen(path);
        char const * dir = path;
#ifdef __APPLE__
        if (!dir_len) { dir = "."; dir_len = 1; }
#endif
        size_t prefix = dir_len ? dir_len + 1 : 0;
        if (prefix < sizeof(file) && name_len < sizeof(file) - prefix) {
            if (dir_len) { memcpy(file, dir, dir_len); file[dir_len] = '/'; }
            memcpy(file + prefix, name, name_len + 1);
            int err = child_exec_one(file, argv, sh_argv, envp);
            if (!err || !child_search_next(file, err)) return;
        } else {
#ifdef __APPLE__
            constexpr char start[] = "execvP: ", finish[] = ": path too long\n";
            child_write(start, sizeof(start) - 1);
            child_write(dir, dir_len);
            child_write(finish, sizeof(finish) - 1);
#else
            // A single component longer than the search buffer is skipped; a
            // representable component with an overlong executable path is terminal.
            if (dir_len < sizeof(file)) return;
#endif
        }
        if (!end) return;
        path = end + 1;
    }
}

#endif

static obj_res spawn(string_ref const & proc_name, array_ref<string_ref> const & args, stdio stdin_mode, stdio stdout_mode,
  stdio stderr_mode, option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env,
  bool inherit_env, bool do_setsid) try {
    /* Setup stdio based on process configuration. */
    auto stdin_pipe  = setup_stdio(stdin_mode);
    auto stdout_pipe = setup_stdio(stdout_mode);
    auto stderr_pipe = setup_stdio(stderr_mode);

    // Adopt the parent endpoints before fork, so fdopen failures cannot leave a running child.
    // Keep their descriptor numbers for the child's close calls after ownership is transferred.
    int parent_stdin_fd = stdin_pipe ? stdin_pipe->m_write_fd : -1;
    int parent_stdout_fd = stdout_pipe ? stdout_pipe->m_read_fd : -1;
    int parent_stderr_fd = stderr_pipe ? stderr_pipe->m_read_fd : -1;
    object_ref parent_stdin  = stdin_pipe  ? parent_pipe_handle(*stdin_pipe, true)   : object_ref();
    object_ref parent_stdout = stdout_pipe ? parent_pipe_handle(*stdout_pipe, false) : object_ref();
    object_ref parent_stderr = stderr_pipe ? parent_pipe_handle(*stderr_pipe, false) : object_ref();

    process_args pargs;
    pargs.push(proc_name.data());
    for (auto & arg : args) pargs.push(arg.data());
    pargs.finish();
    char ** argv = pargs.data();
#if defined(__APPLE__) || defined(__GLIBC__)
    std::vector<char *> shell_args;
    shell_args.reserve(args.size() + 3);
#ifdef __APPLE__
    shell_args.push_back(argv[0]);
#else
    shell_args.push_back(const_cast<char *>("/bin/sh"));
#endif
    shell_args.push_back(nullptr);  // candidate script name, written in the child
    for (size_t i = 1; i <= args.size() + 1; ++i) shell_args.push_back(argv[i]);
    char ** sh_argv = shell_args.data();
    std::string default_path = default_exec_path();
    char const * default_path_data = default_path.c_str();
#endif
    char *** inherited_slot = process_environ_slot();
    child_environment environment(inherit_env, *inherited_slot, env);
    char ** prepared_env = environment.pointers.empty() ? nullptr : environment.pointers.data();
    char const * directory = cwd ? cwd.get()->data() : nullptr;
    std::string cwd_error = directory ? std::string("could not change directory to ") + directory + "\n" : "";
    std::string exec_error = std::string("could not execute external process '") + argv[0] + "'\n";
    char const * cwd_msg = cwd_error.data();
    size_t cwd_len = cwd_error.size();
    char const * exec_msg = exec_error.data();
    size_t exec_len = exec_error.size();
    auto source = [](stdio mode, int fd) { return mode == PIPED ? fd : mode == NUL ? null_stdio : inherit_stdio; };
    int sources[] = { source(stdin_mode, stdin_pipe ? stdin_pipe->m_read_fd : -1),
                      source(stdout_mode, stdout_pipe ? stdout_pipe->m_write_fd : -1),
                      source(stderr_mode, stderr_pipe ? stderr_pipe->m_write_fd : -1) };
    int parent_fds[] = { parent_stdin_fd, parent_stdout_fd, parent_stderr_fd };

    pid_t pid = fork_process();
    if (pid == 0) {
        for (int fd : parent_fds) if (fd >= 0) close(fd);
        for (int i = 0; i != 3; ++i) {
            if (!child_redirect(sources[i], i)) {
                constexpr char msg[] = "could not redirect child standard stream\n";
                child_fail(msg, sizeof(msg) - 1);
            }
        }
        if (directory && chdir(directory) < 0) child_fail(cwd_msg, cwd_len);
        if (do_setsid && setsid() < 0) {
            constexpr char msg[] = "could not create child session\n";
            child_fail(msg, sizeof(msg) - 1);
        }
        char * empty_env[] = { nullptr };
        char ** envp = prepared_env ? prepared_env : *inherited_slot;
        if (!envp) envp = empty_env;
#if defined(__APPLE__) || defined(__GLIBC__)
        char const * path = default_path_data;
        for (char ** p = envp; *p; ++p) {
            if (strncmp(*p, "PATH=", 5) == 0) { path = *p + 5; break; }
        }
        child_exec(argv, sh_argv, envp, path);
#else
        // Other libcs have different PATH and ENOEXEC rules. Preserve the host's
        // execvp policy; the environment array is prepared before fork.
        *inherited_slot = envp;
        execvp(argv[0], argv);
#endif
        child_fail(exec_msg, exec_len);
    } else if (pid == -1) {
        throw errno;
    }

    // The child owns these endpoints after fork; the parent's FILE wrappers own the others.
    if (stdin_pipe) stdin_pipe->close_read();
    if (stdout_pipe) stdout_pipe->close_write();
    if (stderr_pipe) stderr_pipe->close_write();

    object_ref r = mk_cnstr(0, parent_stdin, parent_stdout, parent_stderr, sizeof(pid_t) + sizeof(uint8_t));
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    cnstr_set_uint32(r.raw(), 3 * sizeof(object *), pid);
    cnstr_set_uint8(r.raw(), 3 * sizeof(object *) + sizeof(pid_t), do_setsid);
    return lean_io_result_mk_ok(r.steal());
} catch (std::bad_alloc const &) {
    throw ENOMEM;
}

extern "C" LEAN_EXPORT obj_res lean_io_process_child_take_stdin(b_obj_arg, obj_arg lchild) {
    object_ref child(lchild);
    object_ref child2 = mk_cnstr(0, object_ref(box(0)), cnstr_get_ref(child, 1), cnstr_get_ref(child, 2), sizeof(pid_t) + sizeof(uint8_t));
    cnstr_set_uint32(child2.raw(), 3 * sizeof(object *), cnstr_get_uint32(child.raw(), 3 * sizeof(object *)));
    cnstr_set_uint8(child2.raw(), 3 * sizeof(object *) + sizeof(pid_t),
        cnstr_get_uint8(child.raw(), 3 * sizeof(object *) + sizeof(pid_t)));
    object_ref r = mk_cnstr(0, cnstr_get_ref(child, 0), child2);
    return lean_io_result_mk_ok(r.steal());
}

void initialize_process() {}
void finalize_process() {}

#endif

extern "C" lean_object* lean_mk_io_error_other_error(uint32_t, lean_object*);

extern "C" LEAN_EXPORT obj_res lean_io_process_spawn(obj_arg args_) {
    object_ref args(args_);
    object_ref stdio_cfg = cnstr_get_ref(args, 0);
    stdio stdin_mode  = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 0));
    stdio stdout_mode = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 1));
    stdio stderr_mode = static_cast<stdio>(cnstr_get_uint8(stdio_cfg.raw(), 2));
    if (stdin_mode == stdio::INHERIT) {
        std::cout.flush();
    }
    try {
        return spawn(
                cnstr_get_ref_t<string_ref>(args, 1),
                cnstr_get_ref_t<array_ref<string_ref>>(args, 2),
                stdin_mode,
                stdout_mode,
                stderr_mode,
                cnstr_get_ref_t<option_ref<string_ref>>(args, 3),
                cnstr_get_ref_t<array_ref<pair_ref<string_ref, option_ref<string_ref>>>>(args, 4),
                cnstr_get_uint8(args.raw(), 5 * sizeof(object *)),
                cnstr_get_uint8(args.raw(), 5 * sizeof(object *) + 1));
#if defined(LEAN_WINDOWS)
    } catch (std::bad_alloc const &) {
        return lean_io_result_mk_error(decode_io_error(ENOMEM, nullptr));
    } catch (std::length_error const &) {
        return lean_io_result_mk_error(decode_io_error(E2BIG, nullptr));
#endif
    } catch (int err) {
        return lean_io_result_mk_error(decode_io_error(err, nullptr));
    } catch (std::system_error const & err) {
        // TODO: decode
        return lean_io_result_mk_error(lean_mk_io_error_other_error(err.code().value(), mk_string(err.code().message())));
    }
}

}
