/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/flet.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/replace_visitor.h"
#include "library/fun_info.h"
#include "library/annotation.h"
#include "library/idx_metavar.h"
#include "library/matcher.h"

namespace lean {
static level lift_idx_metaunivs(level const & l, unsigned u_offset) {
    if (!has_meta(l) || u_offset == 0)
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) return some_level(l);
            if (is_idx_metauniv(l))
                return some_level(mk_idx_metauniv(to_meta_idx(l) + u_offset));
            else
                return none_level();
        });
}

static levels lift_idx_metaunivs(levels const & ls, unsigned u_offset) {
    return map_reuse(ls,
                     [&](level const & l) { return lift_idx_metaunivs(l, u_offset); },
                     [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
}

class lift_idx_metavars_fn : public replace_visitor {
    unsigned m_u_offset;
    unsigned m_e_offset;

    virtual expr visit_meta(expr const & m) override {
        if (is_idx_metavar(m)) {
            expr new_type = visit(mlocal_type(m));
            return mk_idx_metavar(to_meta_idx(m) + m_e_offset, new_type);
        } else {
            return replace_visitor::visit_meta(m);
        }
    }

    virtual expr visit_sort(expr const & e) override {
        return update_sort(e, lift_idx_metaunivs(sort_level(e), m_u_offset));
    }

    virtual expr visit_constant(expr const & e) override {
        return update_constant(e, lift_idx_metaunivs(const_levels(e), m_u_offset));
    }

    virtual expr visit(expr const & e) override {
        if ((!has_univ_metavar(e) || m_u_offset == 0) && (!has_expr_metavar(e) || m_e_offset == 0))
            return e;
        return replace_visitor::visit(e);
    }

public:
    lift_idx_metavars_fn(unsigned u_offset, unsigned e_offset):
        m_u_offset(u_offset), m_e_offset(e_offset) {
    }
};

static expr lift_idx_metavars(expr const & t, unsigned u_offset, unsigned e_offset) {
    if ((!has_univ_metavar(t) || u_offset == 0) && (!has_expr_metavar(t) || e_offset == 0))
        return t;
    return lift_idx_metavars_fn(u_offset, e_offset)(t);
}

expr matcher::lift_idx_metavars(expr const & t) const {
    return ::lean::lift_idx_metavars(t, m_u_offset, m_e_offset);
}

optional<level> matcher::get_assignment(level const & l) const {
    lean_assert(is_idx_metauniv(l));
    return m_ctx.get_tmp_uvar_assignment(to_meta_idx(l) + m_u_offset);
}

void matcher::assign(level const & u, level const & v) {
    m_ctx.assign_tmp(to_meta_idx(u) + m_u_offset, v);
}

static bool is_max_like(level const & l) {
    return is_max(l) || is_imax(l);
}

bool matcher::has_assigned(level const & l) const {
    if (!has_meta(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (!has_meta(l))
                return false; // stop search
            if (found)
                return false;  // stop search
            if (is_idx_metauniv(l) && get_assignment(l)) {
                found = true;
                return false; // stop search
            }
            return true; // continue search
        });
    return found;
}

level matcher::instantiate_mvars(level const & l) const {
    if (!has_assigned(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) {
                return some_level(l);
            } else if (is_idx_metauniv(l)) {
                if (auto v = get_assignment(l))
                    return some_level(*v);
                else
                    return some_level(l);
            } else {
                return none_level();
            }
        });
}

bool matcher::match(level const & p, level const & t) {
    if (is_equivalent(p, t))
        return true;

    if (is_idx_metauniv(p)) {
        if (auto v = get_assignment(p)) {
            return match(*v, t);
        } else {
            assign(p, t);
            return true;
        }
    }

    level new_p = instantiate_mvars(p);
    if (p != new_p)
        return match(new_p, t);

    if (p.kind() != t.kind() && (is_succ(p) || is_succ(t))) {
        if (optional<level> pred_p = dec_level(p))
        if (optional<level> pred_t = dec_level(t))
            return match(*pred_p, *pred_t);
    }

    if ((is_max_like(p) || is_max_like(t)) && m_mode != Final) {
        m_u_postponed.emplace_back(p, t);
        return true;
    }

    if (p.kind() != t.kind())
        return false;

    switch (p.kind()) {
    case level_kind::Max:
        return
            match(max_lhs(p), max_lhs(t)) &&
            match(max_rhs(p), max_rhs(t));
    case level_kind::IMax:
        return
            match(imax_lhs(p), imax_lhs(p)) &&
            match(imax_rhs(t), imax_rhs(t));
    case level_kind::Succ:
        return match(succ_of(p), succ_of(t));
    case level_kind::Param:
    case level_kind::Meta:
        return false;
    case level_kind::Zero:
        lean_unreachable();
    }
    lean_unreachable();
}

bool matcher::match(levels const & ps, levels const & ts) {
    if (is_nil(ps) && is_nil(ts)) {
        return true;
    } else if (!is_nil(ps) && !is_nil(ts)) {
        return
            match(head(ps), head(ts)) &&
            match(tail(ps), tail(ts));
    } else {
        return false;
    }
}

optional<expr> matcher::get_assignment(expr const & e) const {
    lean_assert(is_idx_metavar(e));
    return m_ctx.get_tmp_mvar_assignment(to_meta_idx(e) + m_e_offset);
}

void matcher::assign(expr const & m, expr const & v) {
    m_ctx.assign_tmp(to_meta_idx(m) + m_e_offset, v);
}

bool matcher::match_binding_binding(expr p, expr t) {
    lean_assert(p.kind() == t.kind());
    lean_assert(is_binding(p));
    expr_kind k = p.kind();
    type_context::tmp_locals locals(m_ctx);
    do {
        optional<expr> var_p_type;
        if (binding_domain(p) != binding_domain(t)) {
            var_p_type      = instantiate_rev(binding_domain(p), locals.size(), locals.data());
            expr var_t_type = instantiate_rev(binding_domain(t), locals.size(), locals.data());
            if (!match(*var_p_type, var_t_type))
                return false;
        }
        if (!closed(binding_body(p)) || !closed(binding_body(t))) {
            // local is used inside p or t
            if (!var_p_type)
                var_p_type = instantiate_rev(binding_domain(p), locals.size(), locals.data());
            locals.push_local(binding_name(p), *var_p_type);
        } else {
            expr const & dont_care = mk_Prop();
            locals.push_local(binding_name(p), dont_care);
        }
        p = binding_body(p);
        t = binding_body(t);
    } while (p.kind() == k && t.kind() == k);
    return match(instantiate_rev(p, locals.size(), locals.data()),
                 instantiate_rev(t, locals.size(), locals.data()));
}

optional<expr> matcher::reduce_cheap(expr const & t) const {
    if (is_annotation(t))
        return some_expr(get_annotation_arg(t));
    if (is_let(t))
        return some_expr(instantiate(let_body(t), let_value(t)));
    expr new_t = head_beta_reduce(t);
    if (new_t != t)
        return some_expr(new_t);
    return none_expr();
}

bool matcher::match_macro_macro(expr const & p, expr const & t) {
    return false;
}

optional<expr> matcher::zeta(expr const & e) {
    if (!is_local_decl_ref(e))
        return none_expr();
    if (auto d = m_ctx.lctx().find_local_decl(e)) {
        if (auto v = d->get_value())
            return some_expr(*v);
    }
    return none_expr();
}

optional<expr> matcher::delta(expr const & e) {
    // TODO(Leo)
    return none_expr();
}

bool matcher::match_local_local(expr const & p, expr const & t) {
    lean_assert(p != t);
    if (auto new_t = zeta(t)) {
        return match(p, *new_t);
    } else if (auto new_p = zeta(p)) {
        return match(*new_p, t);
    } else {
        return false;
    }
}

bool matcher::match_const_const(expr const & p, expr const & t) {
    if (const_name(p) == const_name(t)) {
        return match(const_levels(p), const_levels(t));
    } else if (auto new_t = delta(t)) {
        return match(p, *new_t);
    } else if (auto new_p = delta(p)) {
        return match(*new_p, t);
    } else {
        return false;
    }
}

/* Reduce ((let x := v in b) a_1 ... a_n) into (b[x/v] a_1 ... a_n) */
static expr unfold_let_app_core(expr const & e) {
    buffer<expr> args;
    expr const & f = get_app_rev_args(e, args);
    lean_assert(is_let(f));
    expr new_f = instantiate(let_body(f), let_value(f));
    return apply_beta(new_f, args.size(), args.data());
}

static optional<expr> unfold_let_app(expr const & e) {
    if (is_let(get_app_fn(e)))
        return some_expr(unfold_let_app_core(e));
    else
        return none_expr();
}

optional<expr> matcher::unfold_local_definition(expr const & e) {
    buffer<expr> args;
    expr const & f = get_app_rev_args(e, args);
    if (auto new_f = zeta(f))
        return some_expr(apply_beta(*new_f, args.size(), args.data()));
    else
        return none_expr();
}

bool matcher::match_args(expr const & f, expr const & p, expr const & t) {
    buffer<expr> p_args, t_args;
    get_app_args(p, p_args);
    get_app_args(t, t_args);
    if (p_args.size() != t_args.size())
        return false;

    unsigned i = 0;
    if (m_mode == Regular) {
        /* In Regular mode, we match explicit arguments first, and postpone implicit ones. */
        fun_info finfo = get_fun_info(m_ctx, f, p_args.size());
        for (param_info const & pinfo : finfo.get_params_info()) {
            if (pinfo.is_implicit() || pinfo.is_inst_implicit()) {
                m_e_postponed.emplace_back(m_ctx.lctx(), p_args[i], t_args[i]);
            } else if (!match(p_args[i], t_args[i])) {
                return false;
            }
            i++;
        }
    }

    for (; i < p_args.size(); i++) {
        if (!match(p_args[i], t_args[i]))
            return false;
    }
    return true;
}

optional<expr> matcher::unfold_const_app(expr const &) {
    // TODO(Leo)
    return none_expr();
}

bool matcher::is_reducible(name const & n) {
    // TODO(Leo)
    return false;
}

bool matcher::match_app_app(expr const & p, expr const & t) {
    expr const & p_fn = get_app_fn(p);
    expr const & t_fn = get_app_fn(t);
    lean_assert(!is_lambda(p_fn));
    lean_assert(!is_lambda(t_fn));

    if (is_idx_metavar(p_fn)) {
        if (auto v = get_assignment(p_fn)) {
            buffer<expr> p_args;
            get_app_rev_args(p, p_args);
            expr new_p = apply_beta(*v, p_args.size(), p_args.data());
            return match(new_p, t);
        }
        // TODO(Leo)
    }

    if (is_constant(p_fn) && is_constant(t_fn)) {
        if (const_name(p_fn) == const_name(t_fn)) {
            if (!match(const_levels(p_fn), const_levels(t_fn)))
                return false;
            if (!is_reducible(const_name(p_fn))) {
                return match_args(t_fn, p, t);
            } else if (auto new_t = unfold_const_app(t)) {
                return match(p, *new_t);
            } else if (auto new_p = unfold_const_app(p)) {
                return match(*new_p, t);
            } else {
                return false;
            }
        } else if (auto new_t = unfold_const_app(t)) {
            return match(p, *new_t);
        } else if (auto new_p = unfold_const_app(p)) {
            return match(*new_p, t);
        } else {
            return false;
        }
    } else if (is_local(p_fn) && is_local(t_fn)) {
        if (p_fn == t_fn) {
            if (!zeta(t_fn)) {
                return match_args(t_fn, p, t);
            } else {
                if (auto new_p = unfold_local_definition(p))
                if (auto new_t = unfold_local_definition(t))
                    return match(*new_p, *new_t);
                return false;
            }
        } else if (auto new_t = unfold_local_definition(t)) {
            return match(p, *new_t);
        } else if (auto new_p = unfold_local_definition(p)) {
            return match(*new_p, t);
        } else {
            return false;
        }
    } else if (auto new_t = unfold_local_definition(t)) {
        return match(p, *new_t);
    } else if (auto new_p = unfold_local_definition(p)) {
        return match(*new_p, t);
    } else if (is_let(t_fn)) {
        return match(p, unfold_let_app_core(t));
    } else if (is_let(p_fn)) {
        return match(unfold_let_app_core(p), t);
    } else if (auto new_t = unfold_const_app(t)) {
        return match(p, *new_t);
    } else if (auto new_p = unfold_const_app(p)) {
        return match(*new_p, t);
    } else {
        return false;
    }
}

optional<expr> matcher::eta_expand_right(expr const & t) {
    lean_assert(!is_lambda(t));
    expr type = m_ctx.relaxed_whnf(m_ctx.infer(t));
    if (!is_pi(type))
        return none_expr();
    return some_expr(mk_lambda(binding_name(type), binding_domain(type), mk_app(t, Var(0))));
}

expr matcher::eta_expand_left(expr const & p, expr const & t) {
    lean_assert(!is_lambda(p));
    lean_assert(is_lambda(t));
    return mk_lambda(binding_name(t), binding_domain(t), mk_app(p, Var(0)));
}

bool matcher::match_proof_irrel(expr const & p, expr const & t) {
    expr t_type = m_ctx.infer(t);
    if (m_ctx.is_prop(t_type)) {
        expr p_type = m_ctx.infer(lift_idx_metavars(p));
        return m_ctx.is_def_eq(p_type, t_type);
    } else {
        return false;
    }
}

bool matcher::match(expr const & p, expr const & t) {
    if (p == t)
        return true;

    if (is_idx_metavar(p)) {
        if (auto v = get_assignment(p)) {
            return match(*v, t);
        } else {
            assign(p, t);
            return true;
        }
    }

    if (auto new_t = reduce_cheap(t))
        return match(p, *new_t);
    if (auto new_p = reduce_cheap(p))
        return match(*new_p, t);

    if (p.kind() == t.kind()) {
        switch (p.kind()) {
        case expr_kind::Lambda: case expr_kind::Pi:
            return match_binding_binding(p, t);
        case expr_kind::Sort:
            return match(sort_level(p), sort_level(t));
        case expr_kind::Meta:
            return false;
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Let:
             /* reduce_cheap should take of this case */
            lean_unreachable();
        case expr_kind::Macro:
            return match_macro_macro(p, t);
        case expr_kind::Local:
            return match_local_local(p, t);
        case expr_kind::Constant:
            return match_const_const(p, t);
        case expr_kind::App:
            return match_app_app(p, t);
        }
    }

    if (is_lambda(p)) {
        if (auto new_t = eta_expand_right(t)) {
            return match(p, *new_t);
        } else {
            /* This can only happen if the type of t is not a Pi (type error). */
            return false;
        }
    } else if (is_lambda(t)) {
        return match(eta_expand_left(p, t), t);
    } else if (auto new_t = unfold_local_definition(t)) {
        return match(p, *new_t);
    } else if (auto new_t = unfold_let_app(t)) {
        return match(p, *new_t);
    } else if (auto new_p = unfold_local_definition(p)) {
        return match(*new_p, t);
    } else if (auto new_p = unfold_let_app(p)) {
        return match(*new_p, t);
    } else if (match_proof_irrel(p, t)) {
        return true;
    } else if (auto new_t = delta(t)) {
        return match(p, *new_t);
    } else if (auto new_t = unfold_const_app(t)) {
        return match(p, *new_t);
    } else if (auto new_p = delta(p)) {
        return match(*new_p, t);
    } else if (auto new_p = unfold_const_app(p)) {
        return match(*new_p, t);
    } else {
        return false;
    }
}
}
