/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
/** \brief Create a universe level metavariable that can be used as a placeholder in #match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In the match procedure the substitution is also efficiently represented as an array (aka buffer).
*/
level mk_idx_metauniv(unsigned i);
/** \brief Return true iff \c l is a metauniverse created using \c mk_idx_metauniv */
bool is_idx_metauniv(level const & l);
unsigned to_meta_idx(level const & l);

/** \brief Create a special metavariable that can be used as a placeholder in #match.

    \remark The index \c i is encoded in the hierarchical name, and can be quickly accessed.
    In the match procedure the substitution is also efficiently represented as an array (aka buffer).
*/
expr mk_idx_metavar(unsigned i, expr const & type);
/** \brief Return true iff \c l is a metavariable created using \c mk_idx_metavar */
bool is_idx_metavar(expr const & l);
unsigned to_meta_idx(expr const & e);

/** \brief Return true iff \c e contains idx metavariables or universe metavariables */
bool has_idx_metavar(expr const & e);


/** \brief Return a new expression where index of idx_metauniv variables is increased by udelta,
    and idx_metavars by mdelta */
expr lift_idx_metavars(expr const & e, unsigned udelta, unsigned mdelta);
level lift_idx_metaunivs(level const & l, unsigned udelta);

void initialize_idx_metavar();
void finalize_idx_metavar();
}
