/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <utility>
#include <vector>
#include "kernel/expr.h"

// `Lean.Expr.instantiateLevelParams` in native code (`instantiateLevelParamsNative`): the traversal
// of `Expr.replace` with `instantiateLevelParamsCore.replaceFn`, which calls back into Lean only for
// the `const` and `sort` nodes with level parameters. As there, subterms without level parameters
// are returned as they are, and the results of shared subterms are cached by their address.

// `instantiateLevelParamsLeaf` (an `@[export]` function, so its arguments are owned)
extern "C" lean_object * lean_paperlean_inst_lparams_leaf(lean_object * e, lean_object * ps, lean_object * us);

namespace lean {
namespace {
class inst_lparams_fn {
    // open addressing; the keys are subterms of the input, which keeps them alive; the values are owned
    std::vector<std::pair<lean_object *, lean_object *>> m_tab;
    size_t m_count = 0;
    b_obj_arg m_ps, m_us;

    static size_t hash(lean_object * p) {
        size_t x = reinterpret_cast<size_t>(p) >> 3;
        x ^= x >> 17;
        x *= 0x9E3779B97F4A7C15ull;
        return x ^ (x >> 29);
    }
    lean_object * find(lean_object * k) const {
        if (m_tab.empty()) return nullptr;
        size_t m = m_tab.size() - 1, i = hash(k) & m;
        while (m_tab[i].first) {
            if (m_tab[i].first == k) return m_tab[i].second;
            i = (i + 1) & m;
        }
        return nullptr;
    }
    void grow() {
        std::vector<std::pair<lean_object *, lean_object *>> old;
        old.swap(m_tab);
        m_tab.assign(old.empty() ? 64 : old.size() * 2, {nullptr, nullptr});
        size_t m = m_tab.size() - 1;
        for (auto & kv : old) {
            if (!kv.first) continue;
            size_t i = hash(kv.first) & m;
            while (m_tab[i].first) i = (i + 1) & m;
            m_tab[i] = kv;
        }
    }
    void insert(lean_object * k, lean_object * v) {
        if (2 * (m_count + 1) > m_tab.size()) grow();
        size_t m = m_tab.size() - 1, i = hash(k) & m;
        while (m_tab[i].first) i = (i + 1) & m;
        lean_inc(v);
        m_tab[i] = {k, v};
        m_count++;
    }
    expr save(expr const & e, expr r, bool shared) {
        if (shared) insert(e.raw(), r.raw());
        return r;
    }
    expr apply(expr const & e) {
        if (!has_param_univ(e)) return e;
        // an exclusive subterm occurs once, so its result is not looked up again
        bool shared = !lean_is_exclusive(e.raw());
        if (shared) {
            if (lean_object * r = find(e.raw())) {
                lean_inc(r);
                return expr(r);
            }
        }
        switch (e.kind()) {
        case expr_kind::Const: case expr_kind::Sort:
            lean_inc(e.raw()); lean_inc(m_ps); lean_inc(m_us);
            return save(e, expr(lean_paperlean_inst_lparams_leaf(e.raw(), m_ps, m_us)), shared);
        case expr_kind::MData:
            return save(e, update_mdata(e, apply(mdata_expr(e))), shared);
        case expr_kind::Proj:
            return save(e, update_proj(e, apply(proj_expr(e))), shared);
        case expr_kind::App: {
            expr f = apply(app_fn(e));
            expr a = apply(app_arg(e));
            return save(e, update_app(e, f, a), shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr d = apply(binding_domain(e));
            expr b = apply(binding_body(e));
            return save(e, update_binding(e, d, b), shared);
        }
        case expr_kind::Let: {
            expr t = apply(let_type(e));
            expr v = apply(let_value(e));
            expr b = apply(let_body(e));
            return save(e, update_let(e, t, v, b), shared);
        }
        default:
            return save(e, e, shared);
        }
    }
public:
    inst_lparams_fn(b_obj_arg ps, b_obj_arg us) : m_ps(ps), m_us(us) {}
    ~inst_lparams_fn() {
        for (auto & kv : m_tab)
            if (kv.first) lean_dec(kv.second);
    }
    expr operator()(expr const & e) { return apply(e); }
};
}
}

/* instantiateLevelParamsNative (e : @& Expr) (paramNames : List Name) (lvls : List Level) : Expr */
extern "C" LEAN_EXPORT lean_object * lean_paperlean_instantiate_level_params(lean::b_obj_arg e, lean::obj_arg ps,
                                                                             lean::obj_arg us) {
    lean_object * r;
    {
        lean::inst_lparams_fn fn(ps, us);
        r = fn(lean::expr(e, true)).steal();
    }
    lean_dec(ps);
    lean_dec(us);
    return r;
}

/* nativeAvailable (dummy : @& α) : Bool -- `true`, except in the stage0 shim */
extern "C" LEAN_EXPORT uint8_t lean_paperlean_native_available(lean::b_obj_arg) {
    return true;
}
