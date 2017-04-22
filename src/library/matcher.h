/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
class matcher {
    enum mode { ReadOnly, Regular, Full, Final };

    struct u_constraint {
        level            m_pattern;
        level            m_term;
        u_constraint(level const & p, level const & t):m_pattern(p), m_term(t) {}
    };

    struct e_constraint {
        local_context    m_lctx;
        expr             m_pattern;
        expr             m_term;
    };

    type_context &       m_ctx;
    buffer<u_constraint> m_u_postponed;
    buffer<e_constraint> m_e_postponed;
    unsigned             m_u_offset;
    unsigned             m_e_offset;
    mode                 m_mode;

    optional<level> get_assignment(level const & l) const;
    void assign(level const & u, level const & v);
    bool has_assigned(level const & l) const;
    level instantiate_mvars(level const & l) const;
    bool match(level const & p, level const & t);
    bool match(levels const & ps, levels const & ts);

    optional<expr> get_assignment(expr const & e) const;
    void assign(expr const & m, expr const & v);
    bool match_binding(local_context const & lctx, expr p, expr t);
    bool match(local_context const & lctx, expr const & p, expr const & t);

    matcher(type_context & ctx):m_ctx(ctx) {}
};
}
