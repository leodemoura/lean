/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/metavar_context.h"
#include "library/equations_compiler/equations.h"
namespace lean {
class elaborator;
expr compile_equations(equations_context & ectx, expr const & eqns);
void initialize_compiler();
void finalize_compiler();
}
