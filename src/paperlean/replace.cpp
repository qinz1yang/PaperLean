/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <algorithm>
#include "kernel/expr.h"

// `instantiate` and `instantiateRange` of `Lean.Expr` for PaperLean's beta reduction in `whnf`
// (`Lean.PaperLean.exprInstantiate`, `Lean.PaperLean.betaRev`): the computation of
// `kernel/instantiate.cpp`, with its caching of shared subterms, but with the callback inlined and the
// cache in one flat table. The kernel keeps its own code, and so do the `@[extern]` functions of
// `Lean.Expr`, which compiled code calls.

namespace lean {
namespace {
// open addressing on (subterm, offset); the keys are subterms of the input, which keeps them alive,
// the values are owned; the first entries need no allocation
class flat_cache {
    struct entry { lean_object * k; unsigned off; lean_object * v; };
    static constexpr size_t inline_size = 32;
    entry m_inline[inline_size];
    entry * m_tab = m_inline;
    size_t m_size = inline_size;
    size_t m_count = 0;

    static size_t hash(lean_object * p, unsigned off) {
        size_t x = (reinterpret_cast<size_t>(p) >> 3) + off * 0x9E3779B97F4A7C15ull;
        x ^= x >> 17;
        x *= 0x9E3779B97F4A7C15ull;
        return x ^ (x >> 29);
    }
    void put(entry * tab, size_t size, entry const & e) {
        size_t m = size - 1, i = hash(e.k, e.off) & m;
        while (tab[i].k) i = (i + 1) & m;
        tab[i] = e;
    }
    void grow() {
        size_t size = m_size * 2;
        entry * tab = new entry[size];
        std::fill(tab, tab + size, entry{nullptr, 0, nullptr});
        for (size_t i = 0; i < m_size; i++)
            if (m_tab[i].k) put(tab, size, m_tab[i]);
        if (m_tab != m_inline) delete[] m_tab;
        m_tab = tab;
        m_size = size;
    }
public:
    flat_cache() { std::fill(m_inline, m_inline + inline_size, entry{nullptr, 0, nullptr}); }
    flat_cache(flat_cache const &) = delete;
    ~flat_cache() {
        for (size_t i = 0; i < m_size; i++)
            if (m_tab[i].k) lean_dec(m_tab[i].v);
        if (m_tab != m_inline) delete[] m_tab;
    }
    lean_object * find(lean_object * k, unsigned off) const {
        size_t m = m_size - 1, i = hash(k, off) & m;
        while (m_tab[i].k) {
            if (m_tab[i].k == k && m_tab[i].off == off) return m_tab[i].v;
            i = (i + 1) & m;
        }
        return nullptr;
    }
    void insert(lean_object * k, unsigned off, lean_object * v) {
        if (2 * (m_count + 1) > m_size) grow();
        lean_inc(v);
        put(m_tab, m_size, entry{k, off, v});
        m_count++;
    }
};

// `replace_rec_fn` of `kernel/replace_fn.cpp` with the cache
template<class F> class replace_fn {
    F m_f;
    flat_cache m_cache;

    expr save(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared) m_cache.insert(e.raw(), offset, r.raw());
        return r;
    }
public:
    explicit replace_fn(F const & f) : m_f(f) {}
    expr operator()(expr const & e, unsigned offset) {
        bool shared = false;
        if (!is_likely_unshared(e)) {
            if (lean_object * r = m_cache.find(e.raw(), offset)) {
                lean_inc(r);
                return expr(r);
            }
            shared = true;
        }
        if (optional<expr> r = m_f(e, offset))
            return save(e, offset, std::move(*r), shared);
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
        case expr_kind::BVar:  case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            return save(e, offset, e, shared);
        case expr_kind::MData: {
            expr new_e = (*this)(mdata_expr(e), offset);
            return save(e, offset, update_mdata(e, new_e), shared);
        }
        case expr_kind::Proj: {
            expr new_e = (*this)(proj_expr(e), offset);
            return save(e, offset, update_proj(e, new_e), shared);
        }
        case expr_kind::App: {
            expr new_f = (*this)(app_fn(e), offset);
            expr new_a = (*this)(app_arg(e), offset);
            return save(e, offset, update_app(e, new_f, new_a), shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = (*this)(binding_domain(e), offset);
            expr new_b = (*this)(binding_body(e), offset + 1);
            return save(e, offset, update_binding(e, new_d, new_b), shared);
        }
        case expr_kind::Let: {
            expr new_t = (*this)(let_type(e), offset);
            expr new_v = (*this)(let_value(e), offset);
            expr new_b = (*this)(let_body(e), offset + 1);
            return save(e, offset, update_let(e, new_t, new_v, new_b), shared);
        }
        }
        lean_unreachable();
    }
};

template<class F> expr meta_replace(expr const & e, F const & f) {
    return replace_fn<F>(f)(e, 0);
}

// `lift_loose_bvars(e, 0, d)` of `kernel/expr.cpp`
expr lift_bvars(expr const & e, unsigned d) {
    if (d == 0 || get_loose_bvar_range(e) == 0)
        return e;
    return meta_replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            unsigned s1 = offset;
            if (s1 >= get_loose_bvar_range(m))
                return some_expr(m);
            if (is_bvar(m) && bvar_idx(m) >= offset)
                return some_expr(mk_bvar(bvar_idx(m) + nat(d)));
            return none_expr();
        });
}

// `lean_expr_instantiate_core` of `kernel/instantiate.cpp`
object * instantiate_core(b_obj_arg a0, size_t n, object ** subst) {
    expr const & a = reinterpret_cast<expr const &>(a0);
    if (!has_loose_bvars(a) || n == 0) {
        lean_inc(a0);
        return a0;
    }
    expr r = meta_replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (offset >= get_loose_bvar_range(m))
                return some_expr(m);
            if (is_bvar(m)) {
                nat const & vidx = bvar_idx(m);
                if (vidx >= offset) {
                    size_t h = offset + n;
                    if (h < offset || (vidx.is_small() && vidx.get_small_value() < h)) {
                        object * v = subst[vidx.get_small_value() - offset];
                        return some_expr(lift_bvars(TO_REF(expr, v), offset));
                    } else {
                        return some_expr(mk_bvar(vidx - nat::of_size_t(n)));
                    }
                }
            }
            return none_expr();
        });
    return r.steal();
}

void check_range(b_obj_arg begin, b_obj_arg end, b_obj_arg subst, char const * fn) {
    if (!lean_is_scalar(begin) || !lean_is_scalar(end) || lean_unbox(begin) > lean_unbox(end) ||
        lean_unbox(end) > lean_array_size(subst))
        lean_internal_panic(fn);
}
}
}

using namespace lean; // NOLINT

/* exprInstantiate (e : @& Expr) (subst : @& Array Expr) : Expr */
extern "C" LEAN_EXPORT object * lean_paperlean_expr_instantiate(b_obj_arg a, b_obj_arg subst) {
    return instantiate_core(a, lean_array_size(subst), lean_array_cptr(subst));
}

/* exprInstantiateRange (e : @& Expr) (beginIdx endIdx : @& Nat) (subst : @& Array Expr) : Expr */
extern "C" LEAN_EXPORT object * lean_paperlean_expr_instantiate_range(b_obj_arg a, b_obj_arg begin, b_obj_arg end,
                                                                      b_obj_arg subst) {
    check_range(begin, end, subst, "invalid range for Expr.instantiateRange");
    return instantiate_core(a, lean_unbox(end) - lean_unbox(begin), lean_array_cptr(subst) + lean_unbox(begin));
}

/* replaceFVarLeaves (e : @& Expr) (f : @& (Expr → Option Expr)) : Expr */
extern "C" LEAN_EXPORT object * lean_paperlean_tc_replace_fvars(b_obj_arg a, b_obj_arg f) {
    expr const & e = TO_REF(expr, a);
    if (!has_fvar(e)) {
        lean_inc(a);
        return a;
    }

    auto replace_fvar = [f](expr const & t, unsigned) -> optional<expr> {
        if (!has_fvar(t))
            return some_expr(t);
        if (!is_fvar(t))
            return none_expr();

        lean_inc(t.raw());
        lean_inc_ref(f);
        object * r = lean_apply_1(f, t.raw());
        if (lean_is_scalar(r))
            return none_expr();
        expr value(lean_ctor_get(r, 0), true);
        lean_dec_ref(r);
        return some_expr(value);
    };

    if (is_fvar(e)) {
        if (auto r = replace_fvar(e, 0))
            return r->steal();
        lean_inc(a);
        return a;
    }

    expr r = meta_replace(e, replace_fvar);
    return r.steal();
}
