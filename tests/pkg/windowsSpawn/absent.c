/* GUI subsystem: Windows does not supply default console handles to this child. */
#include <stdint.h>
#include <stdlib.h>
#include <wchar.h>
#include <windows.h>

int WINAPI wWinMain(HINSTANCE instance, HINSTANCE previous, PWSTR command, int show) {
    (void)instance; (void)previous; (void)command; (void)show;
    wchar_t layout[4], raw[32];
    if (GetEnvironmentVariableW(L"V023_STD_LAYOUT", layout, 4) != 3) return 2;
    DWORD n = GetEnvironmentVariableW(L"V023_STD_EVENT", raw, 32);
    if (!n || n >= 32) return 3;
    STARTUPINFOW info = {0};
    info.cb = sizeof(info);
    GetStartupInfoW(&info);
    if (!(info.dwFlags & STARTF_USESTDHANDLES)) return 4;
    HANDLE supplied[3] = {info.hStdInput, info.hStdOutput, info.hStdError};
    DWORD ids[3] = {STD_INPUT_HANDLE, STD_OUTPUT_HANDLE, STD_ERROR_HANDLE};
    for (unsigned i = 0; i < 3; ++i) {
        HANDLE actual = GetStdHandle(ids[i]);
        if (layout[i] == L'0') {
            if (actual != NULL || supplied[i] != NULL) return 5;
        } else if (layout[i] == L'N') {
            if (!actual || actual == INVALID_HANDLE_VALUE || GetFileType(actual) != FILE_TYPE_CHAR) return 6;
        } else return 7;
    }
    // Every mode must exclude this real inheritable object owned by the parent.
    SetEvent((HANDLE)(uintptr_t)wcstoull(raw, NULL, 10));
    return 0;
}
