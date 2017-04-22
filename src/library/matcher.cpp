/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/annotation.h"
#include "library/idx_metavar.h"
#include "library/matcher.h"

namespace lean {
optional<level> matcher::get_assignment(level const & l) const {
    lean_assert(is_idx_metavar(l));
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
    lean_assert(m_mode != ReadOnly);
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
        } else if (m_mode != ReadOnly) {
            assign(p, t);
            return true;
        } else {
            return false;
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

    if (is_max_like(p) || is_max_like(t)) {
        if (m_mode != Final) {
            m_u_postponed.emplace_back(p, t);
            return true;
        } else {
            return false;
        }
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
        return match(succ_of(p), succ_of(p));
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

bool matcher::match_binding(local_context const & lctx, expr p, expr t) {
    lean_assert(p.kind() == t.kind());
    lean_assert(is_binding(p));
    expr_kind k = p.kind();
    buffer<expr> locals;
    local_context new_lctx = lctx;
    do {
        optional<expr> var_p_type;
        if (binding_domain(p) != binding_domain(t)) {
            var_p_type      = instantiate_rev(binding_domain(p), locals.size(), locals.data());
            expr var_t_type = instantiate_rev(binding_domain(t), locals.size(), locals.data());
            if (!match(new_lctx, *var_p_type, var_t_type))
                return false;
        }
        if (!closed(binding_body(p)) || !closed(binding_body(t))) {
            // local is used inside p or t
            if (!var_p_type)
                var_p_type = instantiate_rev(binding_domain(p), locals.size(), locals.data());
            locals.push_back(new_lctx.mk_local_decl(binding_name(p), *var_p_type));
        } else {
            expr const & dont_care = mk_Prop();
            locals.push_back(dont_care);
        }
        p = binding_body(p);
        t = binding_body(t);
    } while (p.kind() == k && t.kind() == k);
    return match(new_lctx,
                 instantiate_rev(p, locals.size(), locals.data()),
                 instantiate_rev(t, locals.size(), locals.data()));
}

bool matcher::match(local_context const & lctx, expr const & p, expr const & t) {
    if (p == t)
        return true;

    if (is_idx_metavar(p)) {
        if (auto v = get_assignment(p)) {
            return match(lctx, *v, t);
        } else if (m_mode != ReadOnly) {
            assign(p, t);
            return true;
        } else {
            return false;
        }
    }

    if (is_annotation(p)) {
        return match(lctx, get_annotation_arg(p), t);
    } else if (is_annotation(t)) {
        return match(lctx, p, get_annotation_arg(t));
    }

    // TODO(Leo);
    return false;
}
}
