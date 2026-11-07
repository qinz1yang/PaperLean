/* The actual Windows CRT supplies wargv. This child does not use Lean's encoder. */
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <wchar.h>
#include <windows.h>

static int equals_env(wchar_t const * name, wchar_t const * expected) {
    static wchar_t value[32768];
    DWORD n = GetEnvironmentVariableW(name, value, 32768);
    if (!expected) return n == 0 && GetLastError() == ERROR_ENVVAR_NOT_FOUND;
    return n == wcslen(expected) && wcscmp(value, expected) == 0;
}

static int repeated_env(wchar_t const * name, wchar_t ch) {
    static wchar_t value[32768];
    DWORD n = GetEnvironmentVariableW(name, value, 32768);
    if (n != 16000) return 0;
    for (DWORD i = 0; i < n; ++i) if (value[i] != ch) return 0;
    return 1;
}

int wmain(int argc, wchar_t ** argv) {
    if (argc < 2) return 2;
    if (!wcscmp(argv[1], L"argv")) {
        wchar_t const * want[] = {L"", L"two words", L"a\tb", L"path\\", L"two\\\\", L"a\\\"b",
                                  L"a\\\\\"b", L"\"", L"*?", L"line\nfeed", L"\u03bb\U0001F9EA", L"last"};
        size_t n = sizeof(want)/sizeof(want[0]);
        if ((size_t)argc != n + 2) return 3;
        for (size_t i = 0; i < n; ++i) if (wcscmp(argv[i+2], want[i])) return 4;
    } else if (!wcscmp(argv[1], L"environment")) {
        if (!equals_env(L"V023_KEEP", L"parent") || !equals_env(L"V023_REMOVE", NULL) ||
            !equals_env(L"V023_MIXED", L"last") || !equals_env(L"V023_TEXT", L"\u03bb\U0001F9EA") ||
            !equals_env(L"V023_TAIL", L"present") || !repeated_env(L"V023_A", L'a') ||
            !repeated_env(L"V023_B", L'b') || !repeated_env(L"V023_C", L'c')) return 5;
    } else if (!wcscmp(argv[1], L"isolated")) {
        if (!equals_env(L"V023_KEEP", NULL) || !equals_env(L"V023_ONLY", L"yes")) return 6;
    } else if (!wcscmp(argv[1], L"empty")) {
        if (!equals_env(L"V023_KEEP", NULL) || !equals_env(L"V023_REMOVE", NULL)) return 7;
    } else if (!wcscmp(argv[1], L"handle")) {
        if (argc != 3) return 8;
        // If the unrelated inheritable event leaked into this child, this signals
        // the parent's object. The parent checks the object, not the numeric value.
        SetEvent((HANDLE)(uintptr_t)wcstoull(argv[2], NULL, 10));
    } else if (!wcscmp(argv[1], L"cwd")) {
        if (argc != 3) return 11;
        DWORD size = GetCurrentDirectoryW(0, NULL);
        if (!size) return 12;
        wchar_t * path = (wchar_t *)malloc((size_t)size * sizeof(wchar_t));
        if (!path) return 13;
        DWORD length = GetCurrentDirectoryW(size, path);
        int equal = length && length < size && CompareStringOrdinal(path, -1, argv[2], -1, TRUE) == CSTR_EQUAL;
        free(path);
        if (!equal) return 14;
    } else if (!wcscmp(argv[1], L"stdio")) {
        char input[5] = {0};
        if (fread(input, 1, 4, stdin) != 4 || memcmp(input, "ping", 4)) return 9;
        fputs("pong", stdout);
        fputs("error", stderr);
    } else return 10;
    return 0;
}
