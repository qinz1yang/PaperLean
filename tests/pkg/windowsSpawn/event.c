/* Test-only inheritable event in the actual Lean parent. */
#include <stdint.h>
#include <stdlib.h>
#include <windows.h>
#include <lean/lean.h>

static lean_object * failure(char const * why) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(why)));
}

LEAN_EXPORT lean_object * v023_windows_new_event(void) {
    SECURITY_ATTRIBUTES security = {sizeof(security), NULL, TRUE};
    HANDLE event = CreateEventW(&security, TRUE, FALSE, NULL);
    if (!event) return failure("CreateEventW failed");
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)(uintptr_t)event));
}

LEAN_EXPORT lean_object * v023_windows_event_set(uint64_t raw) {
    DWORD state = WaitForSingleObject((HANDLE)(uintptr_t)raw, 0);
    if (state != WAIT_TIMEOUT && state != WAIT_OBJECT_0) return failure("event wait failed");
    return lean_io_result_mk_ok(lean_box(state == WAIT_OBJECT_0));
}

LEAN_EXPORT lean_object * v023_windows_close_event(uint64_t raw) {
    if (!CloseHandle((HANDLE)(uintptr_t)raw)) return failure("CloseHandle failed");
    return lean_io_result_mk_ok(lean_box(0));
}

/* These hooks alter just the test parent, and never close its saved handles. */
static DWORD const std_ids[] = {STD_INPUT_HANDLE, STD_OUTPUT_HANDLE, STD_ERROR_HANDLE};
static HANDLE saved_std[3];
static unsigned saved_mask;

static int restore_std(void) {
    int ok = 1;
    for (unsigned i = 0; i < 3; ++i) {
        if (saved_mask & (1u << i)) {
            if (SetStdHandle(std_ids[i], saved_std[i])) saved_mask &= ~(1u << i);
            else ok = 0;
        }
    }
    return ok;
}

LEAN_EXPORT lean_object * v023_windows_mask_std(uint8_t mask, uint8_t invalid) {
    if (saved_mask) return failure("nested stdio mask");
    for (unsigned i = 0; i < 3; ++i) {
        if (!(mask & (1u << i))) continue;
        saved_std[i] = GetStdHandle(std_ids[i]);
        if (saved_std[i] == INVALID_HANDLE_VALUE || !SetStdHandle(std_ids[i], invalid ? INVALID_HANDLE_VALUE : NULL)) {
            restore_std();
            return failure("could not replace test stdio");
        }
        saved_mask |= (1u << i);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_object * v023_windows_restore_std(void) {
    return restore_std() ? lean_io_result_mk_ok(lean_box(0)) : failure("could not restore test stdio");
}

/* Use the Windows wide filesystem API to construct independent test inputs. */
LEAN_EXPORT lean_object * v023_windows_test_directory(b_lean_obj_arg path, uint8_t remove) {
    int size = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, lean_string_cstr(path), -1, NULL, 0);
    if (size <= 0) return failure("invalid test directory");
    wchar_t * wide = (wchar_t *)malloc((size_t)size * sizeof(wchar_t));
    if (!wide) return failure("test directory allocation failed");
    int n = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, lean_string_cstr(path), -1, wide, size);
    BOOL ok = n == size && (remove ? RemoveDirectoryW(wide) : CreateDirectoryW(wide, NULL));
    free(wide);
    return ok ? lean_io_result_mk_ok(lean_box(0)) : failure("test directory setup or cleanup failed");
}
