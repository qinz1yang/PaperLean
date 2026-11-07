/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.

Compile this translation unit, not a copied fragment of verify. Only its input-producing Lean
callbacks and dlsym are redirected. The actual verify, owner_of, snapshot and load_lib bodies come
unchanged from the selected native_libs.cpp. The second thread calls the real loader while verify
is stopped at its first module-symbol lookup, which is after it captured toolchain and generation.
*/
#include <chrono>
#include <condition_variable>
#include <dlfcn.h>
#include <mutex>
#include <stdexcept>
#include <thread>
#include "runtime/object.h"

static void * v023_lookup(void *, char const *);
#define dlsym v023_lookup
#define lean_paperlean_native_import_info v023_native_import_info
#define lean_paperlean_env_imports_id v023_env_imports_id
#ifndef V023_NATIVE_LIBS_SOURCE
#define V023_NATIVE_LIBS_SOURCE "paperlean/native_libs.cpp"
#endif
#include V023_NATIVE_LIBS_SOURCE
#undef lean_paperlean_env_imports_id
#undef lean_paperlean_native_import_info
#undef dlsym

#ifndef PAPERLEAN_NATIVE_LIBS
#error "This regression requires the real macOS/Linux native loader (LEAN_MMAP)."
#endif

namespace {
std::mutex barrier_mutex;
std::condition_variable barrier_cv;
bool lookup_waiting = false;
bool load_finished = false;
std::string loader_error;
lean_object * test_info = nullptr;
lean_object * test_datas = nullptr;
constexpr char target_symbol[] = "initialize_V023Later";

void require(bool condition, char const * message) {
    if (!condition) throw std::runtime_error(message);
}

lean_object * one(lean_object * value) {
    return lean_array_push(lean_mk_empty_array_with_capacity(lean_box(1)), value);
}

void make_inputs() {
    // NativeImportInfo: one runtime import from a named package, without init side effects.
    test_info = lean_alloc_ctor(0, 8, 1);
    lean::name module("V023Later");
    lean_inc(module.raw());
    lean_ctor_set(test_info, 0, one(module.raw()));
    lean_ctor_set(test_info, 1, one(lean_box(1)));
    lean_ctor_set(test_info, 2, one(lean_box(0)));
    lean_ctor_set(test_info, 3, one(lean_mk_string(target_symbol)));
    lean_ctor_set(test_info, 4, one(lean_mk_empty_array_with_capacity(lean_box(0))));
    lean_ctor_set(test_info, 5, one(lean_box(0)));
    lean_ctor_set(test_info, 6, one(lean_mk_string("v023-package")));
    lean_ctor_set(test_info, 7, one(lean_box(0)));
    lean_ctor_set_uint8(test_info, sizeof(void *) * 8, 0);
    test_datas = one(lean_box(0));
}
}

namespace lean {
extern "C" obj_res v023_native_import_info(obj_arg env, obj_arg opts) {
    lean_dec(env); lean_dec(opts);
    lean_inc(test_info);
    return test_info;
}
extern "C" obj_res v023_env_imports_id(obj_arg env) {
    lean_dec(env);
    lean_inc(test_datas);
    return test_datas;
}
}

static void * v023_lookup(void * handle, char const * symbol) {
    if (strcmp(symbol, target_symbol) == 0) {
        std::unique_lock<std::mutex> lock(barrier_mutex);
        lookup_waiting = true;
        barrier_cv.notify_all();
        require(barrier_cv.wait_for(lock, std::chrono::seconds(20), [] { return load_finished; }),
                "loader did not finish while verify was at the symbol barrier");
        require(loader_error.empty(), loader_error.c_str());
    }
    return ::dlsym(handle, symbol);
}

extern "C" LEAN_EXPORT lean_obj_res v023_native_snapshot_case(
        b_lean_obj_arg library, b_lean_obj_arg size) {
    // Each case is a fresh process: note_core and the dlopen lifetime are intentionally real.
    try {
        unsetenv("PAPERLEAN_ROOT_PACKAGE");
        unsetenv("PAPERLEAN_NATIVE_STATS");
        make_inputs();
        std::vector<bool> word;
        word.push_back(false);
        size_t count = strcmp(lean_string_cstr(size), "word") == 0 ? word.capacity()
            : static_cast<size_t>(std::stoul(lean_string_cstr(size)));
        require(count == 0 || count == 1 || count == word.capacity(), "unsupported snapshot size");
        require(lean::g_libs->empty(), "fixture must start without package libraries");
        // Padding represents already registered libraries. Only the new owner has a symbol range;
        // all dlopen/range registration/generation changes for that owner use production load_lib.
        for (size_t i = 0; i < count; ++i)
            lean::g_libs->push_back({ "v023-padding-" + std::to_string(i), {}, false });
        lean::manifest m;
        m.path = "v023-in-memory-manifest";
        m.hdr = {};
        require(lean::canonical_path(lean_string_cstr(library), m.data), "library path is invalid");
        m.hdr.lib_path = {0, m.data.size()};
        require(lean::stat_identity(m.data.c_str(), m.hdr.lib), "library identity is unavailable");

        int32_t loaded_owner = -1;
        std::thread loader([&] {
            try {
                {
                    std::unique_lock<std::mutex> lock(barrier_mutex);
                    require(barrier_cv.wait_for(lock, std::chrono::seconds(20), [] { return lookup_waiting; }),
                            "verify never reached its post-snapshot symbol lookup");
                }
                loaded_owner = lean::load_lib(m);
                require(loaded_owner == static_cast<int32_t>(count), "real loader did not append the later owner");
            } catch (std::exception const & e) {
                std::lock_guard<std::mutex> lock(barrier_mutex);
                loader_error = e.what();
            }
            std::lock_guard<std::mutex> lock(barrier_mutex);
            load_finished = true;
            barrier_cv.notify_all();
        });
        lean::native_modules modules;
        std::unordered_map<std::string, std::shared_ptr<lean::native_init const>> inits;
        std::unordered_map<std::string, void *> found;
        uint64_t generation = 0;
        bool used = false;
        std::exception_ptr failure;
        try {
            used = lean::verify(lean_box(0), lean_box(0), "", modules, inits, found, generation);
        } catch (...) { failure = std::current_exception(); }
        loader.join();
        if (failure) std::rethrow_exception(failure);
        require(loader_error.empty(), loader_error.c_str());
        require(lookup_waiting && load_finished, "barrier was not exercised");
        void * address = ::dlsym(RTLD_DEFAULT, target_symbol);
        require(address != nullptr, "loaded initializer is not globally visible");
        require(lean::owner_of(reinterpret_cast<uintptr_t>(address)) == loaded_owner,
                "visible symbol did not resolve to the newly loaded owner");
        require(generation < lean::g_libs_generation.load(), "load did not happen after the captured generation");
        require(!used && modules.lib_of == std::vector<int32_t>{-1}, "later owner became native-qualified");
        require(modules.init_lib == std::vector<int32_t>{-1}, "later owner became an initializer owner");
        require(!lean::any_init_lib(modules) && inits.empty(), "later owner acquired native initializers");
        require(found.count(target_symbol) == 1, "verify did not observe the later symbol");
        printf("native snapshot=%zu later-owner=%d rejected; real verify/load barrier passed\n", count, loaded_owner);
        lean_dec(test_info); lean_dec(test_datas);
        return lean_io_result_mk_ok(lean_box(0));
    } catch (std::exception const & e) {
        return lean::io_result_mk_error(e.what());
    }
}
