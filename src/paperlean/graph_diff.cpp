/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/

/*
Comparison of object graphs, used by `PAPERLEAN_IMPORT=check` to verify that a faster import step
builds exactly the objects of the step it replaces.

The two graphs are traversed in parallel (iteratively: imported environments contain lists with
millions of nodes) while building a bijection between their objects, so that sharing must agree
as well. Objects outside the mimalloc heap (in compacted regions, in particular memory-mapped
`.olean` files) must be the very same object on both sides; they only point to such objects, so
they are not traversed. Heap objects must have the same kind and contents: constructor tag, number
of object fields and scalar bytes (all of `lean_object_byte_size`, whose allocator padding is
zeroed), array sizes and, if `strict`, capacities, string and scalar array contents, closure
functions and arities, thunk/task/ref states.
*/

#include <lean/lean.h>
#include "runtime/object.h"
#include "runtime/mpz.h"

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <deque>
#include <string>
#include <utility>
#include <vector>

namespace {

// ---------------------------------------------------------------------------------------------
// Small utilities and hashing primitives.
// ---------------------------------------------------------------------------------------------

static constexpr uint32_t ROOT_PARENT = 0xffffffffu;

static inline uint64_t mix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ull;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ull;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebull;
    return x ^ (x >> 31);
}

// Whether an object is owned by the mimalloc heap.  Objects in compacted regions (in particular
// objects in memory-mapped `.olean` files) must only match the identical pointer, so this is the
// key test used throughout the file.  Without mimalloc, compacted objects are malloc-backed while
// heap objects either have a reference count or have `m_cs_sz == 0`; a persistent compacted object
// is recognizable by `m_rc == 0` and `m_cs_sz != 0`.
static inline bool is_heap_object(lean_object * o) {
#ifdef LEAN_MIMALLOC
    return mi_is_in_heap_region(o);
#else
    return !(lean_internal_get_rc(o) == 0 && o->m_cs_sz != 0);
#endif
}

static inline uint64_t pointer_table_hash(lean_object * o) {
    return mix64(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(o) >> 3));
}

// ---------------------------------------------------------------------------------------------
// Object layout helpers.  These mirror the child enumeration of `lean_mark_persistent`.
// ---------------------------------------------------------------------------------------------

static size_t ctor_scalar_size(lean_object * o) {
    size_t total = lean_object_byte_size(o);
    size_t start = sizeof(lean_object) + static_cast<size_t>(lean_ctor_num_objs(o)) * sizeof(void *);
    return total >= start ? total - start : 0;
}

static uint8_t * ctor_scalar_ptr(lean_object * o) {
    return lean_ctor_scalar_cptr(o);
}

static size_t child_count(lean_object * o) {
    uint8_t tag = lean_ptr_tag(o);
    if (tag <= LeanMaxCtorTag)
        return lean_ctor_num_objs(o);
    switch (tag) {
    case LeanArray:
        return lean_array_size(o);
    case LeanClosure:
        return lean_closure_num_fixed(o);
    case LeanThunk: {
        lean_thunk_object * t = lean_to_thunk(o);
        lean_object * value = t->m_value;
        lean_object * closure = t->m_closure;
        if (value != nullptr) return 1;
        return closure != nullptr ? 1 : 0;
    }
    case LeanTask:
        return lean_to_task(o)->m_value != nullptr ? 1 : 0;
    case LeanPromise:
        // `lean_mark_persistent` follows the result task object itself; the task frame then
        // follows the value if it is finished.
        return lean_to_promise(o)->m_result != nullptr ? 1 : 0;
    case LeanRef:
        return lean_to_ref(o)->m_value != nullptr ? 1 : 0;
    default:
        return 0;
    }
}

static lean_object * child_at(lean_object * o, size_t i) {
    uint8_t tag = lean_ptr_tag(o);
    if (tag <= LeanMaxCtorTag)
        return lean_ctor_get(o, static_cast<unsigned>(i));
    switch (tag) {
    case LeanArray:
        return lean_array_cptr(o)[i];
    case LeanClosure:
        return lean_closure_arg_cptr(o)[i];
    case LeanThunk: {
        lean_thunk_object * t = lean_to_thunk(o);
        lean_object * value = t->m_value;
        lean_object * closure = t->m_closure;
        return value != nullptr ? value : closure;
    }
    case LeanTask:
        return lean_to_task(o)->m_value;
    case LeanPromise:
        return reinterpret_cast<lean_object *>(lean_to_promise(o)->m_result);
    case LeanRef:
        return lean_to_ref(o)->m_value;
    default:
        return nullptr;
    }
}

// ---------------------------------------------------------------------------------------------
// Human-readable descriptions used in the first-difference message.
// ---------------------------------------------------------------------------------------------

static std::string hex_u64(uint64_t v) {
    static char const digits[] = "0123456789abcdef";
    char buf[17];
    buf[16] = 0;
    size_t i = 16;
    do {
        buf[--i] = digits[v & 0xf];
        v >>= 4;
    } while (v != 0);
    return std::string(buf + i);
}

static std::string ptr_string(void const * p) {
    return "0x" + hex_u64(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(p)));
}

static std::string hex_bytes(uint8_t const * p, size_t n, size_t max_bytes = 16) {
    std::string r;
    size_t m = n < max_bytes ? n : max_bytes;
    for (size_t i = 0; i < m; ++i) {
        if (i != 0) r.push_back(' ');
        r += hex_u64(p[i]);
    }
    if (n > m) r += " ...";
    return r;
}

static std::string quoted_bytes(char const * p, size_t n, size_t max_bytes = 32) {
    std::string r = "\"";
    size_t m = n < max_bytes ? n : max_bytes;
    for (size_t i = 0; i < m; ++i) {
        unsigned char c = static_cast<unsigned char>(p[i]);
        switch (c) {
        case '\\': r += "\\\\"; break;
        case '"':  r += "\\\""; break;
        case '\n': r += "\\n"; break;
        case '\r': r += "\\r"; break;
        case '\t': r += "\\t"; break;
        default:
            if (c >= 32 && c < 127) {
                r.push_back(static_cast<char>(c));
            } else {
                r += "\\x";
                r += hex_u64(c);
            }
        }
    }
    if (n > m) r += "...";
    r.push_back('"');
    return r;
}

static std::string tag_label(uint8_t tag) {
    if (tag <= LeanMaxCtorTag)
        return "ctor tag " + std::to_string(static_cast<unsigned>(tag));
    switch (tag) {
    case LeanPromise:     return "promise";
    case LeanClosure:     return "closure";
    case LeanArray:       return "array";
    case LeanStructArray: return "struct array";
    case LeanScalarArray: return "scalar array";
    case LeanString:      return "string";
    case LeanMPZ:         return "mpz";
    case LeanThunk:       return "thunk";
    case LeanTask:        return "task";
    case LeanRef:         return "ref";
    case LeanExternal:    return "external";
    case LeanReserved:    return "reserved";
    default:              return "unknown tag " + std::to_string(static_cast<unsigned>(tag));
    }
}

static std::string describe_object(lean_object * o) {
    if (lean_is_scalar(o))
        return "scalar " + std::to_string(lean_unbox(o));
    uint8_t tag = lean_ptr_tag(o);
    if (tag <= LeanMaxCtorTag) {
        size_t n = ctor_scalar_size(o);
        return "ctor(tag=" + std::to_string(static_cast<unsigned>(tag))
             + ", objs=" + std::to_string(lean_ctor_num_objs(o))
             + ", scalar=" + std::to_string(n) + "B"
             + (n != 0 ? " [" + hex_bytes(ctor_scalar_ptr(o), n) + "]" : "")
             + ")";
    }
    switch (tag) {
    case LeanArray:
        return "array(size=" + std::to_string(lean_array_size(o))
             + ", capacity=" + std::to_string(lean_array_capacity(o)) + ")";
    case LeanScalarArray: {
        size_t elems = lean_sarray_size(o);
        unsigned elem_sz = lean_sarray_elem_size(o);
        size_t bytes = static_cast<size_t>(elem_sz) * elems;
        return "scalar-array(elem=" + std::to_string(elem_sz)
             + ", size=" + std::to_string(elems)
             + ", capacity=" + std::to_string(lean_sarray_capacity(o))
             + ", data=[" + hex_bytes(lean_sarray_cptr(o), bytes) + "])";
    }
    case LeanString:
        return "string(size=" + std::to_string(lean_string_size(o))
             + ", length=" + std::to_string(lean_string_len(o))
             + ", bytes=" + quoted_bytes(lean_string_cstr(o), lean_string_size(o)) + ")";
    case LeanMPZ: {
        std::string s = lean::mpz_value(o).to_string();
        if (s.size() > 64) s = s.substr(0, 64) + "...";
        return "mpz(" + s + ")";
    }
    case LeanClosure:
        return "closure(fun=" + ptr_string(lean_closure_fun(o))
             + ", arity=" + std::to_string(lean_closure_arity(o))
             + ", fixed=" + std::to_string(lean_closure_num_fixed(o)) + ")";
    case LeanThunk:
        return std::string("thunk(") + (lean_to_thunk(o)->m_value != nullptr ? "evaluated" : "unevaluated") + ")";
    case LeanTask:
        return std::string("task(") + (lean_to_task(o)->m_value != nullptr ? "finished" : "unfinished") + ")";
    case LeanPromise:
        return std::string("promise(") + (lean_to_promise(o)->m_result != nullptr
                                            && lean_to_promise(o)->m_result->m_value != nullptr
                                          ? "finished" : "unfinished") + ")";
    case LeanRef:
        return std::string("ref(") + (lean_to_ref(o)->m_value != nullptr ? "set" : "null") + ")";
    case LeanExternal:
        return "external(class=" + ptr_string(lean_get_external_class(o))
             + ", data=" + ptr_string(lean_get_external_data(o)) + ")";
    default:
        return "object(" + tag_label(tag) + ", addr=" + ptr_string(o) + ")";
    }
}

// ---------------------------------------------------------------------------------------------
// Compact open-addressing pointer tables.  They replace std::unordered_map for the hot maps:
// no per-node allocations and a much smaller footprint for millions of objects.
// ---------------------------------------------------------------------------------------------

class PtrMap {
    struct Entry {
        lean_object * key = nullptr;
        lean_object * val = nullptr;
        Entry() = default;
        Entry(lean_object * k, lean_object * v) : key(k), val(v) {}
    };

    std::vector<Entry> m_entries;
    size_t             m_count = 0;

    void insert_no_grow(lean_object * key, lean_object * val) {
        size_t mask = m_entries.size() - 1;
        size_t i = static_cast<size_t>(pointer_table_hash(key)) & mask;
        while (m_entries[i].key != nullptr)
            i = (i + 1) & mask;
        m_entries[i] = Entry(key, val);
        ++m_count;
    }

    void rehash(size_t new_capacity) {
        std::vector<Entry> old(std::move(m_entries));
        m_entries.assign(new_capacity, Entry());
        m_count = 0;
        for (Entry const & e : old) {
            if (e.key != nullptr)
                insert_no_grow(e.key, e.val);
        }
    }

    void grow_if_needed() {
        if ((m_count + 1) * 10 >= m_entries.size() * 7)
            rehash(m_entries.size() * 2);
    }

public:
    PtrMap() : m_entries(1024) {}

    bool find(lean_object * key, lean_object ** out) const {
        size_t mask = m_entries.size() - 1;
        size_t i = static_cast<size_t>(pointer_table_hash(key)) & mask;
        while (m_entries[i].key != nullptr) {
            if (m_entries[i].key == key) {
                *out = m_entries[i].val;
                return true;
            }
            i = (i + 1) & mask;
        }
        return false;
    }

    void insert(lean_object * key, lean_object * val) {
        grow_if_needed();
        insert_no_grow(key, val);
    }
};

// ---------------------------------------------------------------------------------------------
// Local (non-child) content comparison.
// ---------------------------------------------------------------------------------------------

static bool check_ready(lean_object * a, lean_object * b, std::string & why) {
    uint8_t ta = lean_ptr_tag(a);
    uint8_t tb = lean_ptr_tag(b);
    if (ta == LeanTask && tb == LeanTask) {
        if (lean_to_task(a)->m_value == nullptr || lean_to_task(b)->m_value == nullptr) {
            why = "unfinished task";
            return false;
        }
    }
    if (ta == LeanPromise && tb == LeanPromise) {
        lean_task_object * ra = lean_to_promise(a)->m_result;
        lean_task_object * rb = lean_to_promise(b)->m_result;
        if (ra == nullptr || rb == nullptr || ra->m_value == nullptr || rb->m_value == nullptr) {
            why = "unfinished task (promise)";
            return false;
        }
    }
    return true;
}

static bool local_equal(lean_object * a, lean_object * b, bool strict, std::string & why) {
    uint8_t ta = lean_ptr_tag(a);
    uint8_t tb = lean_ptr_tag(b);
    if (ta != tb) {
        if (ta <= LeanMaxCtorTag && tb <= LeanMaxCtorTag)
            why = "ctor tag " + std::to_string(static_cast<unsigned>(ta))
                + " vs " + std::to_string(static_cast<unsigned>(tb));
        else
            why = tag_label(ta) + " vs " + tag_label(tb);
        return false;
    }

    if (ta <= LeanMaxCtorTag) {
        unsigned na = lean_ctor_num_objs(a);
        unsigned nb = lean_ctor_num_objs(b);
        if (na != nb) {
            why = "ctor object-field count " + std::to_string(na) + " vs " + std::to_string(nb);
            return false;
        }
        uint8_t * pa = ctor_scalar_ptr(a);
        uint8_t * pb = ctor_scalar_ptr(b);
        size_t sa = ctor_scalar_size(a);
        size_t sb = ctor_scalar_size(b);
        if (sa != sb) {
            why = "ctor scalar content length " + std::to_string(sa) + " vs " + std::to_string(sb);
            return false;
        }
        if (sa != 0 && std::memcmp(pa, pb, sa) != 0) {
            size_t i = 0;
            while (i < sa && pa[i] == pb[i]) ++i;
            why = "ctor scalar byte " + std::to_string(i)
                + ": 0x" + hex_u64(pa[i]) + " vs 0x" + hex_u64(pb[i]);
            return false;
        }
        return true;
    }

    switch (ta) {
    case LeanArray: {
        size_t sa = lean_array_size(a);
        size_t sb = lean_array_size(b);
        if (sa != sb) {
            why = "array size " + std::to_string(sa) + " vs " + std::to_string(sb);
            return false;
        }
        if (strict) {
            size_t ca = lean_array_capacity(a);
            size_t cb = lean_array_capacity(b);
            if (ca != cb) {
                why = "array capacity " + std::to_string(ca) + " vs " + std::to_string(cb);
                return false;
            }
        }
        return true;
    }
    case LeanScalarArray: {
        unsigned ea = lean_sarray_elem_size(a);
        unsigned eb = lean_sarray_elem_size(b);
        if (ea != eb) {
            why = "scalar-array element size " + std::to_string(ea) + " vs " + std::to_string(eb);
            return false;
        }
        size_t sa = lean_sarray_size(a);
        size_t sb = lean_sarray_size(b);
        if (sa != sb) {
            why = "scalar-array size " + std::to_string(sa) + " vs " + std::to_string(sb);
            return false;
        }
        if (strict) {
            size_t ca = lean_sarray_capacity(a);
            size_t cb = lean_sarray_capacity(b);
            if (ca != cb) {
                why = "scalar-array capacity " + std::to_string(ca) + " vs " + std::to_string(cb);
                return false;
            }
        }
        size_t bytes = static_cast<size_t>(ea) * sa;
        if (bytes != 0 && std::memcmp(lean_sarray_cptr(a), lean_sarray_cptr(b), bytes) != 0) {
            why = "scalar-array data bytes differ";
            return false;
        }
        return true;
    }
    case LeanString: {
        size_t sa = lean_string_size(a);
        size_t sb = lean_string_size(b);
        if (sa != sb) {
            why = "string size " + std::to_string(sa) + " vs " + std::to_string(sb);
            return false;
        }
        size_t la = lean_string_len(a);
        size_t lb = lean_string_len(b);
        if (la != lb) {
            why = "string length " + std::to_string(la) + " vs " + std::to_string(lb);
            return false;
        }
        if (sa != 0 && std::memcmp(lean_string_cstr(a), lean_string_cstr(b), sa) != 0) {
            why = "string bytes differ";
            return false;
        }
        return true;
    }
    case LeanMPZ:
        if (!(lean::mpz_value(a) == lean::mpz_value(b))) {
            why = "mpz value differs";
            return false;
        }
        return true;
    case LeanClosure: {
        if (lean_closure_fun(a) != lean_closure_fun(b)) {
            why = "closure function pointer differs";
            return false;
        }
        if (lean_closure_arity(a) != lean_closure_arity(b)) {
            why = "closure arity " + std::to_string(lean_closure_arity(a))
                + " vs " + std::to_string(lean_closure_arity(b));
            return false;
        }
        if (lean_closure_num_fixed(a) != lean_closure_num_fixed(b)) {
            why = "closure fixed-argument count " + std::to_string(lean_closure_num_fixed(a))
                + " vs " + std::to_string(lean_closure_num_fixed(b));
            return false;
        }
        return true;
    }
    case LeanThunk: {
        bool ea = lean_to_thunk(a)->m_value != nullptr;
        bool eb = lean_to_thunk(b)->m_value != nullptr;
        if (ea != eb) {
            why = "thunk evaluation state differs";
            return false;
        }
        if (!ea) {
            bool ca = lean_to_thunk(a)->m_closure != nullptr;
            bool cb = lean_to_thunk(b)->m_closure != nullptr;
            if (ca != cb) {
                why = "thunk closure presence differs";
                return false;
            }
        }
        return true;
    }
    case LeanTask:
        // Unfinished tasks are rejected by check_ready.
        return true;
    case LeanPromise:
        // Unfinished promises are rejected by check_ready.
        return true;
    case LeanRef: {
        bool va = lean_to_ref(a)->m_value != nullptr;
        bool vb = lean_to_ref(b)->m_value != nullptr;
        if (va != vb) {
            why = "ref null state differs";
            return false;
        }
        return true;
    }
    case LeanExternal:
        if (lean_get_external_class(a) != lean_get_external_class(b)) {
            why = "external class pointer differs";
            return false;
        }
        if (lean_get_external_data(a) != lean_get_external_data(b)) {
            why = "external data pointer differs";
            return false;
        }
        return true;
    default:
        why = "unsupported object kind: " + tag_label(ta);
        return false;
    }
}

// ---------------------------------------------------------------------------------------------
// Iterative graph comparison.
// ---------------------------------------------------------------------------------------------

struct DiffFrame {
    lean_object * a;
    lean_object * b;
    uint32_t      parent;      // index into the stack, ROOT_PARENT for the root
    uint32_t      edge_index;  // index of this object in its parent's child sequence
    size_t        next;        // next child to compare
};

static std::string edge_label(lean_object * parent, uint32_t index) {
    uint8_t tag = lean_ptr_tag(parent);
    if (tag <= LeanMaxCtorTag)
        return ".f" + std::to_string(index);
    switch (tag) {
    case LeanArray:
        return ".a[" + std::to_string(index) + "]";
    case LeanClosure:
        return ".c[" + std::to_string(index) + "]";
    case LeanThunk:
    case LeanTask:
    case LeanPromise:
    case LeanRef:
        return ".val";
    default:
        return ".?";
    }
}

static std::string build_path(std::deque<DiffFrame> const & stack, uint32_t parent,
                              uint32_t edge_index, bool has_edge) {
    std::vector<std::string> rev;
    bool at_root = false;

    if (has_edge) {
        rev.push_back(edge_label(stack[parent].a, edge_index));
    }

    uint32_t idx = parent;
    while (rev.size() < 40) {
        // Frame 0 is the root and contributes no edge label.
        if (idx == 0 || idx == ROOT_PARENT) {
            at_root = true;
            break;
        }
        DiffFrame const & f = stack[idx];
        rev.push_back(edge_label(stack[f.parent].a, f.edge_index));
        idx = f.parent;
    }

    // If the loop stopped exactly at the root after the fortieth edge, the path is complete and
    // must not be marked as truncated.
    if (idx == 0 || idx == ROOT_PARENT)
        at_root = true;

    std::string path = "root";
    if (!at_root)
        path += "...";
    for (size_t i = rev.size(); i != 0; --i)
        path += rev[i - 1];
    return path;
}

static lean_obj_res mk_some_string(std::string const & s) {
    lean_object * str = lean_mk_string_from_bytes(s.data(), s.size());
    lean_object * some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, str);
    return some;
}

static lean_obj_res failure_message(std::deque<DiffFrame> const & stack, uint32_t parent,
                                    uint32_t edge_index, bool has_edge,
                                    lean_object * a, lean_object * b, std::string const & why) {
    std::string msg = build_path(stack, parent, edge_index, has_edge);
    msg += ": ";
    msg += why;
    msg += "; A: ";
    msg += describe_object(a);
    msg += "; B: ";
    msg += describe_object(b);
    return mk_some_string(msg);
}

class GraphDiffer {
    enum class PairResult { Skip, Traverse, Failed };

    bool      m_strict;
    PtrMap    m_a2b;
    PtrMap    m_b2a;
    std::deque<DiffFrame> m_stack;

    PairResult process_pair(lean_object * a, lean_object * b, std::string & why) {
        if (lean_is_scalar(a) || lean_is_scalar(b)) {
            if (lean_is_scalar(a) && lean_is_scalar(b)) {
                if (lean_unbox(a) == lean_unbox(b))
                    return PairResult::Skip;
                why = "scalar " + std::to_string(lean_unbox(a))
                    + " vs " + std::to_string(lean_unbox(b));
            } else if (lean_is_scalar(a)) {
                why = "scalar vs " + tag_label(lean_ptr_tag(b));
            } else {
                why = tag_label(lean_ptr_tag(a)) + " vs scalar";
            }
            return PairResult::Failed;
        }

        bool ha = is_heap_object(a);
        bool hb = is_heap_object(b);

        if (a == b) {
            lean_object * mapped = nullptr;
            if (m_a2b.find(a, &mapped)) {
                if (mapped != a) {
                    why = "pointer is already matched with a different object";
                    return PairResult::Failed;
                }
                lean_object * back = nullptr;
                if (!m_b2a.find(a, &back) || back != a) {
                    why = "bijection is inconsistent for an already matched pointer";
                    return PairResult::Failed;
                }
                return PairResult::Skip;
            }
            if (m_b2a.find(a, &mapped)) {
                why = "pointer is already matched with a different object";
                return PairResult::Failed;
            }
            // A compacted object only points to compacted objects, which must coincide as well.
            if (!ha)
                return PairResult::Skip;
            if (!check_ready(a, b, why))
                return PairResult::Failed;
            m_a2b.insert(a, a);
            m_b2a.insert(a, a);
            return PairResult::Traverse;
        }

        lean_object * mapped = nullptr;
        if (m_a2b.find(a, &mapped)) {
            if (mapped != b) {
                why = "A-side object is already matched with a different B-side object";
                return PairResult::Failed;
            }
            lean_object * back = nullptr;
            if (!m_b2a.find(b, &back) || back != a) {
                why = "bijection is inconsistent for an already matched pair";
                return PairResult::Failed;
            }
            return PairResult::Skip;
        }
        if (m_b2a.find(b, &mapped)) {
            why = "B-side object is already matched with a different A-side object";
            return PairResult::Failed;
        }

        // Not strict: empty arrays outside the heap (closed terms of different modules) are alike.
        if (!m_strict && !ha && !hb && !lean_is_scalar(a) && !lean_is_scalar(b) && lean_is_array(a) &&
            lean_is_array(b) && lean_array_size(a) == 0 && lean_array_size(b) == 0)
            return PairResult::Skip;
        if (!ha || !hb) {
            why = "non-heap object identity differs (A=" + ptr_string(a)
                + ", B=" + ptr_string(b) + ")";
            return PairResult::Failed;
        }

        if (!check_ready(a, b, why))
            return PairResult::Failed;
        if (!local_equal(a, b, m_strict, why))
            return PairResult::Failed;

        m_a2b.insert(a, b);
        m_b2a.insert(b, a);
        return PairResult::Traverse;
    }

public:
    explicit GraphDiffer(bool strict) : m_strict(strict) {}

    lean_obj_res run(lean_object * a, lean_object * b) {
        std::string why;
        PairResult r = process_pair(a, b, why);
        if (r == PairResult::Failed)
            return failure_message(m_stack, ROOT_PARENT, 0, false, a, b, why);
        if (r == PairResult::Traverse) {
            DiffFrame root{a, b, ROOT_PARENT, 0, 0};
            m_stack.push_back(root);
        }

        while (!m_stack.empty()) {
            DiffFrame & f = m_stack.back();
            lean_object * fa = f.a;
            lean_object * fb = f.b;
            size_t n = child_count(fa);
            if (f.next >= n) {
                m_stack.pop_back();
                continue;
            }
            size_t idx = f.next;
            f.next = idx + 1;
            lean_object * ca = child_at(fa, idx);
            lean_object * cb = child_at(fb, idx);
            uint32_t parent = static_cast<uint32_t>(m_stack.size() - 1);
            uint32_t edge = idx > 0xffffffffull ? 0xffffffffu : static_cast<uint32_t>(idx);

            PairResult pr = process_pair(ca, cb, why);
            if (pr == PairResult::Failed)
                return failure_message(m_stack, parent, edge, true, ca, cb, why);
            if (pr == PairResult::Traverse) {
                DiffFrame child{ca, cb, parent, edge, 0};
                m_stack.push_back(child);
            }
        }
        return lean_box(0);
    }
};

} // namespace

// ---------------------------------------------------------------------------------------------
// Exported entry points.
// ---------------------------------------------------------------------------------------------

extern "C" LEAN_EXPORT lean_obj_res lean_paperlean_graph_diff(b_lean_obj_arg a, b_lean_obj_arg b, uint8_t strict) {
    GraphDiffer differ(strict != 0);
    return differ.run(a, b);
}

