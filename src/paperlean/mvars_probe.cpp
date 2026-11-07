/*
Copyright (c) 2026 PaperLean contributors.
Released under Apache 2.0 license as described in the file LICENSE.
*/
#include <vector>
#include "kernel/expr.h"

// Whether `instantiateMVars` (`library/instantiate_mvars.cpp`) leaves an expression and the
// metavariable context as they are: when no metavariable that it reaches is assigned, no level
// metavariable either, and no delayed-assigned one has an assigned pending metavariable (whose value
// its first pass would normalize).

extern "C" lean_object * lean_get_lmvar_assignment(lean_object * mctx, lean_object * mid);
extern "C" lean_object * lean_get_mvar_assignment(lean_object * mctx, lean_object * mid);
extern "C" lean_object * lean_get_delayed_mvar_assignment(lean_object * mctx, lean_object * mid);
extern "C" lean_object * lean_delayed_mvar_assignment_mvar_id_pending(lean_object * d);

namespace lean {
namespace {
class mvars_instantiated_fn {
    b_obj_arg m_mctx;
    // Pointers to shared expression and universe nodes visited in this input DAG.
    std::vector<lean_object *> m_seen;
    size_t m_count = 0;

    static size_t hash(lean_object * p) {
        size_t x = reinterpret_cast<size_t>(p) >> 3;
        x ^= x >> 17;
        x *= 0x9E3779B97F4A7C15ull;
        return x ^ (x >> 29);
    }
    // whether `p` was visited before; marks it visited
    bool seen(lean_object * p) {
        if (2 * (m_count + 1) > m_seen.size()) {
            std::vector<lean_object *> old;
            old.swap(m_seen);
            m_seen.assign(old.empty() ? 64 : old.size() * 2, nullptr);
            for (lean_object * q : old)
                if (q) {
                    size_t i = hash(q) & (m_seen.size() - 1);
                    while (m_seen[i]) i = (i + 1) & (m_seen.size() - 1);
                    m_seen[i] = q;
                }
        }
        size_t m = m_seen.size() - 1, i = hash(p) & m;
        while (m_seen[i]) {
            if (m_seen[i] == p) return true;
            i = (i + 1) & m;
        }
        m_seen[i] = p;
        m_count++;
        return false;
    }
    // whether `get` finds an assignment of `mid`
    bool assigned(lean_object * (*get)(lean_object *, lean_object *), name const & mid) {
        lean_inc(m_mctx);
        lean_object * r = get(m_mctx, mid.to_obj_arg());
        bool some = !lean_is_scalar(r);
        lean_dec(r);
        return some;
    }
    bool visit_level(level const & l) {
        if (!has_mvar(l)) return true;
        if (is_shared(l) && seen(l.raw())) return true;
        switch (l.kind()) {
        case level_kind::Succ: return visit_level(succ_of(l));
        case level_kind::Max: case level_kind::IMax: return visit_level(level_lhs(l)) && visit_level(level_rhs(l));
        case level_kind::MVar: return !assigned(lean_get_lmvar_assignment, mvar_id(l));
        default: return true;
        }
    }
    bool visit_mvar(expr const & e) {
        name const & mid = mvar_name(e);
        if (assigned(lean_get_mvar_assignment, mid)) return false;
        lean_inc(m_mctx);
        lean_object * d = lean_get_delayed_mvar_assignment(m_mctx, mid.to_obj_arg());
        if (lean_is_scalar(d)) return true;
        lean_object * a = lean_ctor_get(d, 0);
        lean_inc(a);
        lean_dec(d);
        name pending(lean_delayed_mvar_assignment_mvar_id_pending(a));
        return !assigned(lean_get_mvar_assignment, pending);
    }
    bool visit(expr const & e) {
        if (!has_mvar(e)) return true;
        if (is_shared(e) && seen(e.raw())) return true;
        switch (e.kind()) {
        case expr_kind::Sort: return visit_level(sort_level(e));
        case expr_kind::Const:
            for (level const & l : const_levels(e))
                if (!visit_level(l)) return false;
            return true;
        case expr_kind::MVar: return visit_mvar(e);
        case expr_kind::MData: return visit(mdata_expr(e));
        case expr_kind::Proj: return visit(proj_expr(e));
        case expr_kind::App: return visit(app_fn(e)) && visit(app_arg(e));
        case expr_kind::Pi: case expr_kind::Lambda: return visit(binding_domain(e)) && visit(binding_body(e));
        case expr_kind::Let: return visit(let_type(e)) && visit(let_value(e)) && visit(let_body(e));
        default: return true;
        }
    }
public:
    explicit mvars_instantiated_fn(b_obj_arg mctx) : m_mctx(mctx) {}
    bool operator()(expr const & e) { return visit(e); }
};
}
}

/* mvarsInstantiated (mctx : @& MetavarContext) (e : @& Expr) : Bool */
extern "C" LEAN_EXPORT uint8_t lean_paperlean_mvars_instantiated(lean::b_obj_arg mctx, lean::b_obj_arg e) {
    return lean::mvars_instantiated_fn(mctx)(lean::expr(e, true));
}
