// Copyright (c) 2026 PaperLean contributors. Released under Apache 2.0.
#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <thread>
#include <vector>
#ifdef __APPLE__
#include <mach/mach.h>
#else
#include <dirent.h>
#endif

extern "C" void lean_initialize_runtime_module();
extern "C" unsigned char lean_uv_event_loop_alive();

static int thread_count() {
#ifdef __APPLE__
    thread_act_array_t threads;
    mach_msg_type_number_t count;
    if (task_threads(mach_task_self(), &threads, &count) != KERN_SUCCESS) return -1;
    for (unsigned i = 0; i < count; ++i)
        mach_port_deallocate(mach_task_self(), threads[i]);
    vm_deallocate(mach_task_self(), reinterpret_cast<vm_address_t>(threads), count * sizeof(thread_t));
    return count;
#else
    // Lean's own threads only: on Linux, libuv's default loop (created by the runtime's initialization,
    // as in official Lean) may use io_uring with a kernel submission-queue polling thread, which is listed
    // here as `iou-sqp-<pid>`; it is the kernel's, not a libuv worker of the runtime.
    DIR * dir = opendir("/proc/self/task");
    if (!dir) return -1;
    int count = 0;
    while (auto * e = readdir(dir)) {
        if (e->d_name[0] == '.') continue;
        char path[64], comm[32] = {0};
        std::snprintf(path, sizeof(path), "/proc/self/task/%s/comm", e->d_name);
        if (FILE * f = std::fopen(path, "r")) {
            if (!std::fgets(comm, sizeof(comm), f)) comm[0] = 0;
            std::fclose(f);
        }
        if (std::strncmp(comm, "iou-sqp-", 8) == 0) continue;
        ++count;
    }
    closedir(dir);
    return count;
#endif
}

int main() {
    int initial = thread_count();
    lean_initialize_runtime_module();
    if (initial < 1 || thread_count() != initial) {
        std::fputs("runtime started an unused worker\n", stderr);
        return 1;
    }
    constexpr int n = 12;
    std::atomic<int> ready{0}, alive{0};
    std::vector<std::thread> threads;
    for (int i = 0; i < n; ++i) threads.emplace_back([&] {
        ++ready;
        while (ready.load() != n) std::this_thread::yield();
        if (lean_uv_event_loop_alive()) ++alive;
    });
    for (auto & t : threads) t.join();
    if (alive.load() != n) return 2;
    for (int i = 0; i < 100 && thread_count() != initial + 1; ++i)
        std::this_thread::sleep_for(std::chrono::milliseconds(2));
    if (thread_count() != initial + 1) {
        std::fputs("concurrent first requests must share exactly one worker\n", stderr);
        return 3;
    }
}
