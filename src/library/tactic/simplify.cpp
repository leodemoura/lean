/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "library/tactic/simplify.h"

namespace lean {
auto simplify_core_fn::pre(expr const &, optional<expr> const &) -> optional<result> {
    return optional<result>();
}

auto simplify_core_fn::post(expr const &, optional<expr> const &) -> optional<result> {
    return optional<result>();
}

simp_result simplify_core_fn::join(simp_result const & r1, simp_result const & r2) {
    return ::lean::join(m_ctx, m_rel, r1, r2);
}

void simplify_core_fn::inc_num_steps() {
    m_num_steps++;
    if (m_num_steps > m_max_steps)
        throw exception("simplify failed, maximum number of steps exceeded");
}

simp_result simplify_core_fn::visit_lambda(expr const & e, optional<expr> const &) {
    // TODO(Leo)
    return simp_result(e);
}

simp_result simplify_core_fn::visit_pi(expr const & e, optional<expr> const &) {
    // TODO(Leo)
    return simp_result(e);
}

simp_result simplify_core_fn::visit_let(expr const & e, optional<expr> const &) {
    // TODO(Leo)
    return simp_result(e);
}

simp_result simplify_core_fn::visit_app(expr const & e, optional<expr> const &) {
    // TODO(Leo)
    return simp_result(e);
}

simp_result simplify_core_fn::visit(expr const & e, optional<expr> const & p) {
    check_system("simplify");
    inc_num_steps();

    auto it = m_cache.find(e);
    if (it != m_cache.end())
        return it->second;

    simp_result curr_result(e);
    if (auto r1 = pre(e, p)) {
        if (!r1->second) {
            m_cache.insert(mk_pair(e, r1->first));
            return r1->first;
        }
        curr_result = r1->first;
    }

    while (true) {
        simp_result new_result;
        switch (curr_result.get_new().kind()) {
        case expr_kind::Local:
        case expr_kind::Meta:
        case expr_kind::Sort:
        case expr_kind::Constant:
        case expr_kind::Macro:
            new_result = curr_result;
            break;
        case expr_kind::Var:
            lean_unreachable();
        case expr_kind::Lambda:
            new_result = join(curr_result, visit_lambda(curr_result.get_new(), p));
            break;
        case expr_kind::Pi:
            new_result = join(curr_result, visit_pi(curr_result.get_new(), p));
            break;
        case expr_kind::App:
            new_result = join(curr_result, visit_app(curr_result.get_new(), p));
            break;
        case expr_kind::Let:
            new_result = join(curr_result, visit_let(curr_result.get_new(), p));
            break;
        }

        if (auto r2 = post(new_result.get_new(), p)) {
            if (!r2->second) {
                curr_result = join(new_result, r2->first);
                break;
            } else if (r2->first.get_new() == curr_result.get_new()) {
                break;
            } else {
                /* continue simplifying */
                curr_result = join(new_result, r2->first);
            }
        } else {
            curr_result = new_result;
            break;
        }
    }
    m_cache.insert(mk_pair(e, curr_result));
    return curr_result;
}

simp_result simplify_core_fn::operator()(expr const & e)  {
    simp_result r(e);
    while (true) {
        m_need_restart = false;
        r = join(r, visit(r.get_new(), none_expr()));
        if (!m_need_restart)
            return r;
        m_cache.clear();
    }
}

metavar_context const & simplify_core_fn::mctx() const {
    return m_ctx.mctx();
}
}
