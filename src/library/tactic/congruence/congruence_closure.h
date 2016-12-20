/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/expr_lt.h"
#include "library/type_context.h"
#include "library/congr_lemma_manager.h"

namespace lean {
class congruence_closure {
    class state {
        /* Equivalence class data associated with an expression 'e' */
        struct entry {
            expr           m_next;       // next element in the equivalence class.
            expr           m_root;       // root (aka canonical) representative of the equivalence class.
            expr           m_cg_root;    // root of the congruence class, it is meaningless if 'e' is not an application.
            /* When 'e' was added to this equivalence class because of an equality (H : e = target), then we
               store 'target' at 'm_target', and 'H' at 'm_proof'. Both fields are none if 'e' == m_root */
            optional<expr> m_target;
            optional<expr> m_proof;
            unsigned       m_flipped:1;      // proof has been flipped
            unsigned       m_to_propagate:1; // must be propagated back to state when in equivalence class containing true/false
            unsigned       m_interpreted:1;  // true if the node should be viewed as an abstract value
            unsigned       m_constructor:1;  // true if head symbol is a constructor
            /* m_heq_proofs == true iff some proofs in the equivalence class are based on heterogeneous equality.
               We represent equality and heterogeneous equality in a single equivalence class. */
            unsigned       m_heq_proofs:1;
            unsigned       m_size;           // number of elements in the equivalence class, it is meaningless if 'e' != m_root
            /* The field m_mt is used to implement the mod-time optimization introduce by the Simplify theorem prover.
               The basic idea is to introduce a counter gmt that records the number of heuristic instantiation that have
               occurred in the current branch. It is incremented after each round of heuristic instantiation.
               The field m_mt records the last time any proper descendant of of thie entry was involved in a merge. */
            unsigned       m_mt;
        };

        /* Key for the equality congruence table. */
        struct congr_key {
            expr      m_expr;
            unsigned  m_hash;
        };

        struct congr_key_cmp {
            int operator()(congr_key const & k1, congr_key const & k2) const;
        };

        typedef rb_tree<expr, expr_quick_cmp>                 expr_set;
        typedef rb_map<expr, entry, expr_quick_cmp>           entries;
        typedef rb_tree<expr, expr_quick_cmp>                 parent_occ_set;
        typedef rb_map<expr, parent_occ_set, expr_quick_cmp>  parents;
        typedef rb_tree<congr_key, congr_key_cmp>             congruences;
        typedef rb_map<expr, expr, expr_quick_cmp>            subsingleton_reprs;

        entries            m_entries;
        parents            m_parents;
        congruences        m_congruences;
        /** The following mapping store a representative for each subsingleton type */
        subsingleton_reprs m_subsingleton_reprs;
        /** The congruence closure module has a mode where the root of
            each equivalence class is marked as an interpreted/abstract
            value. Moreover, in this mode proof production is disabled.
            This capability is useful for heuristic instantiation. */
        short              m_froze_partitions{false};
        short              m_inconsistent{false};
        unsigned           m_gmt{0};
        friend class congruence_closure;
    };

    type_context & m_ctx;
    state &        m_state;
public:
    congruence_closure(type_context & ctx, state & s);
};
}
