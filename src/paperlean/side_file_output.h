/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once

#ifndef LEAN_WINDOWS
#include <atomic>
#include <cerrno>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <fcntl.h>
#include <string>
#include <utility>
#include <sys/stat.h>
#include <unistd.h>

namespace lean {
// An exclusive sibling. An abandoned writer never owns a name merely because it
// contains the current PID. Both ordinary publications and cleanup use only the
// entry created by this object.
class side_file_output {
    std::string m_out, m_tmp;
    int m_fd = -1;
    dev_t m_dev{};
    ino_t m_ino{};

    bool owns_name() const {
        struct stat st;
        if (lstat(m_tmp.c_str(), &st) != 0) return false;
        if (st.st_dev == m_dev && st.st_ino == m_ino && S_ISREG(st.st_mode)) return true;
        errno = EIO;
        return false;
    }
    bool close_file() {
        int fd = m_fd;
        m_fd = -1;
        return close(fd) == 0;
    }
public:
    explicit side_file_output(std::string out) : m_out(std::move(out)) {}
    side_file_output(side_file_output const &) = delete;
    side_file_output & operator=(side_file_output const &) = delete;
    ~side_file_output() {
        int saved = errno;
        if (!m_tmp.empty() && owns_name()) unlink(m_tmp.c_str());
        if (m_fd >= 0) close_file();
        errno = saved;
    }

    bool open(mode_t mode) {
        static std::atomic<uint64_t> generation{0};
        for (;;) {
            std::string name = m_out + ".tmp." + std::to_string(getpid()) + "-" +
                std::to_string(generation.fetch_add(1, std::memory_order_relaxed));
            int fd = ::open(name.c_str(), O_CREAT | O_EXCL | O_RDWR | O_CLOEXEC, mode);
            if (fd < 0) {
                if (errno == EINTR || errno == EEXIST) continue;
                return false;
            }
            struct stat st;
            if (fstat(fd, &st) != 0) {
                int saved = errno;
                close(fd);
                errno = saved;
                return false;
            }
            m_fd = fd;
            m_dev = st.st_dev;
            m_ino = st.st_ino;
            m_tmp = std::move(name);
            return true;
        }
    }
    int fd() const { return m_fd; }
    std::string const & path() const { return m_tmp; }

    bool write_bytes(void const * buf, size_t size) {
        auto p = static_cast<char const *>(buf);
        while (size) {
            ssize_t n = write(m_fd, p, size > SSIZE_MAX ? SSIZE_MAX : size);
            if (n < 0 && errno == EINTR) continue;
            if (n == 0) errno = EIO;
            if (n <= 0) return false;
            p += n;
            size -= static_cast<size_t>(n);
        }
        return true;
    }
    // Large packs retain their flock while the associated identity is published.
    bool publish(bool keep_open = false) {
        if (!keep_open && !close_file()) return false;
        if (!owns_name() || std::rename(m_tmp.c_str(), m_out.c_str()) != 0) return false;
        m_tmp.clear();
        return true;
    }
};
}
#endif
