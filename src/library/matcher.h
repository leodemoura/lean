/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {

class matcher {
    enum mode { Explicit, Implicit };

    /*
       Possible configuration options:
       - Backtracking search when processing the implicit part.
         In the current design, we only need backtracking for constraints
         of the form:

                f a =?= f b

         where we first try to solve them by a =?= b, and if it fails
         we backtrack and unfold f.

         One alternative design is to completely avoid backtracking and
         just perform a quick-check where meta-variables are not assigned,
         and constraints are not postponed.

         For example,
                f a =?= f (a + 0)
         would succeed, but
                f ?m =?= f a
         would not.

       - Unfolding when processing explicit part.
         If we index the explicit part using a discrimination tree,
         then unfolding the explicit part would not make a lot of sense.
    */

    struct u_constraint {
        level            m_pattern;
        level            m_term;
    };

    struct e_constraint {
        mode             m_mode;
        local_context    m_lctx;
        expr             m_pattern;
        expr             m_term;
    };

    struct u_constraint_list {
        u_constraint     m_head;
        unsigned         m_tail_idx; /* position at m_u_cells */
    };

    struct e_constraint_list {
        e_constraint     m_head;
        unsigned         m_tail_idx; /* position at m_e_cells */
    };

    struct state {
        unsigned         m_u_curr_list_idx;
        unsigned         m_u_next_list_idx;
        unsigned         m_e_curr_list_idx;
        unsigned         m_e_next_list_idx;
    };

    typedef std::vector<u_constraint_list> u_constraint_lists;
    typedef std::vector<e_constraint_list> e_constraint_lists;

    type_context &       m_ctx;
    u_constraint_lists * m_u_cells;
    e_constraint_lists * m_e_cells;
    unsigned             m_initial_u_cells_size;
    unsigned             m_initial_e_cells_size;
    unsigned             m_u_offset;
    unsigned             m_e_offset;
    state                m_state;
    buffer<state>        m_choices;
};

}
