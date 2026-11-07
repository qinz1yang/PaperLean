/* Focused runtime-ABI regression, patterned after tests/misc_dir/rc_sticky.
   Compile/link against the candidate runtime, then run. No Lean-level type assumptions are needed:
   recorder accesses/checks are opaque non-scalar objects that this test owns explicitly. */
#include <lean/lean.h>
int printf(char const *, ...);
int strcmp(char const *, char const *);
void lean_initialize_runtime_module(void);
lean_obj_res lean_paperlean_env_start_recording(void);
lean_obj_res lean_paperlean_env_without_recording(lean_object *);
lean_obj_res lean_paperlean_env_stop_recording(void);
uint8_t lean_paperlean_env_recording(lean_object *);
lean_obj_res lean_paperlean_env_record(lean_object *, lean_object *, lean_object *);
lean_obj_res lean_paperlean_env_record_all(lean_object *, lean_object *);
lean_obj_res lean_paperlean_env_mark_unusable_io(lean_object *);
uint8_t lean_paperlean_env_pause(void);
lean_obj_res lean_paperlean_env_resume(uint8_t);
void lean_paperlean_env_note_task(void);

static int failures;
#define CHECK(c) do { if (!(c)) { printf("line %d: %s\n", __LINE__, #c); failures++; } } while (0)
static lean_object * leaf(void) { return lean_alloc_ctor(0, 0, 0); }
static void start(void) { lean_dec(lean_paperlean_env_start_recording()); }
static void mark(char const * text) {
    lean_object * why = lean_mk_string(text);
    lean_dec(lean_paperlean_env_mark_unusable_io(why));
    lean_dec(why);
}
static void record(lean_object * a, lean_object * c) {
    lean_inc(a); lean_inc(c);
    CHECK(lean_paperlean_env_record(a, c, lean_box(42)) == lean_box(42));
}
static lean_object * accesses(lean_object * r) { return lean_ctor_get(r, 0); }
static lean_object * checks(lean_object * r) { return lean_ctor_get(lean_ctor_get(r, 1), 0); }
static char const * reason(lean_object * r) { return lean_string_cstr(lean_ctor_get(lean_ctor_get(r, 1), 1)); }
static void check_result(lean_object * r, size_t count, char const * why) {
    CHECK(lean_array_size(accesses(r)) == count);
    CHECK(lean_array_size(checks(r)) == count);
    CHECK(strcmp(reason(r), why) == 0);
}
static void rc(lean_object * o, int n) { CHECK(lean_internal_get_rc(o) == n); }

static void unusable_releases_payload(void) {
    lean_object * a = leaf(), * c = leaf();
    start(); record(a, c); rc(a, 2); rc(c, 2);
    mark("first"); rc(a, 1); rc(c, 1);
    CHECK(lean_paperlean_env_recording(lean_box(0))); /* public predicate unchanged */
    mark("first"); mark("second");
    for (size_t i = 0; i < 10000; i++) record(a, c);
    rc(a, 1); rc(c, 1);
    lean_object * r = lean_paperlean_env_stop_recording();
    check_result(r, 0, "first; second");
    CHECK(!lean_paperlean_env_recording(lean_box(0)));
    lean_dec(r); lean_dec(a); lean_dec(c);
}

static void nested_and_replayed_payload(void) {
    lean_object * a = leaf(), * c = leaf();
    start(); mark("parent"); start(); record(a, c);
    lean_object * child = lean_paperlean_env_stop_recording();
    check_result(child, 1, ""); rc(a, 2); rc(c, 2);
    /* The unusable parent neither copies a usable child's payload nor retains recordAll's. */
    lean_dec(lean_paperlean_env_record_all(accesses(child), checks(child)));
    rc(a, 2); rc(c, 2);
    lean_object * parent = lean_paperlean_env_stop_recording();
    check_result(parent, 0, "parent"); lean_dec(parent);
    start();
    lean_dec(lean_paperlean_env_record_all(accesses(child), checks(child)));
    rc(a, 3); rc(c, 3);
    parent = lean_paperlean_env_stop_recording();
    check_result(parent, 1, "");
    lean_dec(parent); lean_dec(child); rc(a, 1); rc(c, 1);
    /* Usable child into usable parent still copies in order. */
    start(); record(a, c); start(); record(c, a);
    child = lean_paperlean_env_stop_recording(); parent = lean_paperlean_env_stop_recording();
    check_result(child, 1, ""); check_result(parent, 2, "");
    CHECK(lean_array_get_core(accesses(parent), 0) == a);
    CHECK(lean_array_get_core(accesses(parent), 1) == c);
    lean_dec(child); lean_dec(parent); rc(a, 1); rc(c, 1);
    lean_dec(a); lean_dec(c);
}

static lean_object * paused_body(lean_object * unit) {
    CHECK(!lean_paperlean_env_recording(unit));
    mark("withoutRecording"); lean_paperlean_env_note_task();
    return lean_box(42);
}

static void reason_limit(void) {
    static char const * reasons[] = {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9",
        "10", "11", "12", "13", "14", "15", "16", "17"};
    start();
    for (size_t i = 0; i < 18; ++i) { mark(reasons[i]); mark(reasons[i]); }
    lean_object * r = lean_paperlean_env_stop_recording();
    check_result(r, 0, "0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16");
    lean_dec(r);
    start(); mark("parent"); start(); mark("child"); mark("parent");
    r = lean_paperlean_env_stop_recording(); check_result(r, 0, "child; parent"); lean_dec(r);
    r = lean_paperlean_env_stop_recording(); check_result(r, 0, "parent; child"); lean_dec(r);
}

static void nested_invalidation_and_pauses(void) {
    lean_object * a = leaf(), * c = leaf();
    start(); record(a, c); start(); record(c, a);
    lean_paperlean_env_note_task(); mark("child"); mark("child");
    lean_object * child = lean_paperlean_env_stop_recording();
    check_result(child, 0, "a task; child"); rc(a, 1); rc(c, 1);
    mark("later");
    lean_object * parent = lean_paperlean_env_stop_recording();
    check_result(parent, 0, "a task; child; later"); lean_dec(child); lean_dec(parent);
    start(); record(a, c);
    CHECK(lean_paperlean_env_without_recording(lean_alloc_closure((void *)paused_body, 1, 0)) == lean_box(42));
    uint8_t paused = lean_paperlean_env_pause(); CHECK(paused);
    CHECK(!lean_paperlean_env_recording(lean_box(0)));
    lean_paperlean_env_note_task(); mark("paused");
    start(); lean_paperlean_env_note_task();
    child = lean_paperlean_env_stop_recording(); check_result(child, 0, "a task"); lean_dec(child);
    lean_dec(lean_paperlean_env_resume(paused));
    CHECK(lean_paperlean_env_recording(lean_box(0)));
    parent = lean_paperlean_env_stop_recording(); check_result(parent, 1, ""); lean_dec(parent);
    rc(a, 1); rc(c, 1); lean_dec(a); lean_dec(c);
}

int main(void) {
    lean_initialize_runtime_module();
    unusable_releases_payload(); nested_and_replayed_payload(); nested_invalidation_and_pauses(); reason_limit();
    return failures ? 1 : 0;
}
