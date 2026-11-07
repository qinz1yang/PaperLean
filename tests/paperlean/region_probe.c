/* Test-only POSIX helpers; compile with the platform C compiler and candidate Lean headers.
   The saved preferred address is inspected in this native-format fixture (header offset 80).
   No MAP_FIXED is used: an occupied hint is never overwritten. */
#include <lean/lean.h>
#include <errno.h>
#ifdef __APPLE__
#include <mach/mach.h>
#include <mach/mach_vm.h>
#endif
#include <fcntl.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>
static void * reservation;
static size_t reservation_size;
static int file_region(lean_object * path, void ** base, size_t * size) {
    int fd = open(lean_string_cstr(path), O_RDONLY);
    if (fd < 0) return 0;
    struct stat st;
    size_t address;
    int ok = fstat(fd, &st) == 0 && pread(fd, &address, sizeof(address), 80) == sizeof(address);
    close(fd);
    if (!ok || !address || st.st_size <= 0) return 0;
    *base = (void *)address; *size = (size_t)st.st_size;
    return 1;
}
uint8_t lean_region_test_reserve(lean_object * path) {
    void * base; size_t size;
    if (reservation || !file_region(path, &base, &size)) return 0;
    void * p = mmap(base, size, PROT_NONE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (p == MAP_FAILED) return 0;
    if (p != base) { munmap(p, size); return 0; }
    reservation = p; reservation_size = size;
    return 1;
}
lean_obj_res lean_region_test_release(void) {
    if (reservation) munmap(reservation, reservation_size);
    reservation = 0; reservation_size = 0;
    return lean_box(0);
}
/* 0 = absent, 1 = mapped, 2 = probe error. */
uint8_t lean_region_test_mapping(lean_object * path) {
    void * base; size_t size;
    if (!file_region(path, &base, &size)) return 2;
#ifdef __APPLE__
    mach_vm_address_t address = (mach_vm_address_t)base;
    mach_vm_size_t extent = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t count = VM_REGION_BASIC_INFO_COUNT_64;
    mach_port_t object = MACH_PORT_NULL;
    kern_return_t r = mach_vm_region(mach_task_self(), &address, &extent,
        VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &count, &object);
    if (object != MACH_PORT_NULL) mach_port_deallocate(mach_task_self(), object);
    if (r == KERN_INVALID_ADDRESS) return 0;
    if (r != KERN_SUCCESS) return 2;
    return address <= (mach_vm_address_t)base && (mach_vm_address_t)base < address + extent ? 1 : 0;
#else
    unsigned char vec;
    if (mincore(base, 1, &vec) == 0) return 1;
    return errno == ENOMEM ? 0 : 2;
#endif
}
uint64_t lean_region_test_maxrss(void) {
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) != 0) return UINT64_MAX;
#ifdef __APPLE__
    return (uint64_t)usage.ru_maxrss;
#else
    return (uint64_t)usage.ru_maxrss * 1024;
#endif
}
