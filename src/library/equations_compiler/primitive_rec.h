/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
/** \brief Try to eliminate "recursive calls" in the equations \c eqns by using the primitive recursor rec
    (and drec for inductive predicates). */
optional<expr> try_primitive_rec(environment & env, options const & opts,
                                metavar_context & mctx, local_context const & lctx,
                                expr const & eqns);

void initialize_primitive_rec();
void finalize_primitive_rec();
}
