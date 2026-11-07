/* Runtime ownership regression. Retaining a witness reference makes the ownership drop directly
   observable without reading freed memory. Unique references additionally exercise destruction
   under an allocation/leak checker. The ignored Nats exceed size_t and must never be converted. */
#include <lean/lean.h>
lean_obj_res lean_byte_array_copy_slice(b_lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, lean_obj_arg, bool);
int printf(char const *, ...);
void lean_initialize_runtime_module(void);
static int failures;
#define CHECK(c) do { if (!(c)) { printf("line %d: %s\n", __LINE__, #c); failures++; } } while (0)
static lean_object * huge(void) { return lean_cstr_to_nat("184467440737095516160000000000000000000000"); }
int main(void) {
    lean_initialize_runtime_module();
    lean_object * src = lean_alloc_sarray(1, 0, 0);
    lean_object * dest = lean_alloc_sarray(1, 2, 2);
    lean_sarray_cptr(dest)[0] = 17; lean_sarray_cptr(dest)[1] = 29;
    lean_object * off = huge(), * len = huge();
    CHECK(!lean_is_scalar(off)); CHECK(!lean_is_scalar(len));
    lean_inc(off); lean_inc(len);
    lean_object * r = lean_byte_array_copy_slice(src, lean_box(1), dest, off, len, false);
    CHECK(r == dest); CHECK(lean_sarray_size(r) == 2);
    CHECK(lean_sarray_cptr(r)[0] == 17 && lean_sarray_cptr(r)[1] == 29);
    CHECK(lean_internal_get_rc(off) == 1); CHECK(lean_internal_get_rc(len) == 1);
    lean_dec(off); lean_dec(len);
    for (size_t i = 0; i < 10000; i++)
        r = lean_byte_array_copy_slice(src, lean_box(1), r, huge(), huge(), false);
    CHECK(lean_byte_array_copy_slice(src, lean_box(1), r, lean_box(0), lean_box(1), true) == r);
    lean_dec(src);
    src = lean_alloc_sarray(1, 2, 2);
    lean_sarray_cptr(src)[0] = 43; lean_sarray_cptr(src)[1] = 53;
    r = lean_byte_array_copy_slice(src, lean_box(0), r, lean_box(1), lean_box(2), false);
    CHECK(lean_sarray_size(r) == 3);
    CHECK(lean_sarray_cptr(r)[0] == 17 && lean_sarray_cptr(r)[1] == 43 && lean_sarray_cptr(r)[2] == 53);
    lean_dec(src); lean_dec(r);
    return failures ? 1 : 0;
}
