/*
Copyright (c) 2026 PaperLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#pragma once
#include <string>

namespace lean {
// Append one argument after argv[0]. The Microsoft CRT treats that first argument separately.
// A run of n backslashes before a literal quote needs 2n+1 slashes; before the closing quote,
// the run needs 2n. Other backslashes are literal. Always quoting also preserves empty arguments.
template<class String>
inline void append_windows_arg(String & command, String const & arg) {
    using C = typename String::value_type;
    command.push_back(C(' '));
    command.push_back(C('"'));
    typename String::size_type slashes = 0;
    for (C ch : arg) {
        if (ch == C('\\')) {
            ++slashes;
            continue;
        }
        command.append(slashes, C('\\'));
        if (ch == C('"')) {
            command.append(slashes, C('\\'));
            command.push_back(C('\\'));
        }
        command.push_back(ch);
        slashes = 0;
    }
    command.append(slashes, C('\\'));
    command.append(slashes, C('\\'));
    command.push_back(C('"'));
}
}
