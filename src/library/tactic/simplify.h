/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/tactic/simp_result.h"
#include "library/tactic/simp_lemmas.h"

namespace lean {
class simplify_core_fn {
protected:
    typedef expr_struct_map<simp_result> cache;
    type_context & m_ctx;
    cache          m_cache;
    name           m_rel;
    unsigned       m_num_steps;
    bool           m_need_restart;

    unsigned       m_max_steps;
    bool           m_use_funext;
    bool           m_lift_eq;
    simp_lemmas    m_cgr_lemmas;

    typedef pair<simp_result, bool> result;

    virtual optional<result> pre(expr const &, optional<expr> const &);
    virtual optional<result> post(expr const &, optional<expr> const &);

    simp_result join(simp_result const & r1, simp_result const & r2);
    void inc_num_steps();

    virtual simp_result visit_lambda(expr const &, optional<expr> const &);
    virtual simp_result visit_pi(expr const &, optional<expr> const &);
    virtual simp_result visit_let(expr const &, optional<expr> const &);
    virtual simp_result visit_app(expr const &, optional<expr> const &);
    virtual simp_result visit(expr const &, optional<expr> const &);

public:
    simplify_core_fn(type_context & ctx, unsigned max_steps, bool use_funext, bool lift_eq,
                     simp_lemmas const & cgr_lemmas);
    simp_result operator()(expr const & e);
    metavar_context const & mctx() const;
};

class simplify_fn : public simplify_core_fn {
    simp_lemmas m_simp_lemmas;
    virtual optional<result> pre(expr const &, optional<expr> const &) override;
    virtual optional<result> post(expr const &, optional<expr> const &) override;
public:
    simplify_fn(type_context & ctx, unsigned max_steps, bool use_funext, bool lift_eq,
                simp_lemmas const & cgr_lemmas, simp_lemmas const & simp_lemmas);
};

void initialize_simplify();
void finalize_simplify();
}
