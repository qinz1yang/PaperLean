/* Copyright (c) 2026 PaperLean contributors. Released under the Apache 2.0 license. */
#include "runtime/uv/event_loop.h"

extern "C" int v023_uv_configuration_result(int option);
/* Replace only these two host option calls, after including libuv's declarations.
   The error construction, mutex, result ownership and legacy adapter are production code. */
#define uv_loop_configure(loop, option, ...) v023_uv_configuration_result(static_cast<int>(option))
#include "runtime/uv/event_loop.cpp"
