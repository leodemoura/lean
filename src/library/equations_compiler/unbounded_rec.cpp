/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/locals.h"
#include "library/trace.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/elim_match.h"
#include "library/equations_compiler/unbounded_rec.h"
namespace lean {

// #define NEW_CODE

static expr replace_rec_apps(type_context & ctx, expr const & e) {
    equations_header const & header = get_equations_header(e);
    list<name> actual_names = header.m_fn_actual_names;
    unpack_eqns ues(ctx, e);
    buffer<expr> fns;
    buffer<expr> macro_fns;
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        expr const & fn = ues.get_fn(fidx);
        fns.push_back(fn);
#ifdef NEW_CODE
        macro_fns.push_back(mk_rec_fn_macro(head(actual_names), ctx.infer(fn)));
#else
        macro_fns.push_back(mk_rec_fn_macro(mlocal_pp_name(fn), ctx.infer(fn)));
#endif
        actual_names = tail(actual_names);
    }
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        buffer<expr> & eqns = ues.get_eqns_of(fidx);
        for (expr & eqn : eqns) {
            unpack_eqn ue(ctx, eqn);
            expr new_rhs = replace_locals(ue.rhs(), fns, macro_fns);
            ue.rhs() = new_rhs;
            eqn = ue.repack();
        }
    }
    expr r = ues.repack();
    lean_trace("eqn_compiler", tout() << "using unbounded recursion (meta-definition):\n" << r << "\n";);
    return r;
}

eqn_compiler_result unbounded_rec(environment & env, options const & opts,
                   metavar_context & mctx, local_context const & lctx,
                   expr const & e, elaborator & elab) {
    type_context ctx(env, opts, mctx, lctx, transparency_mode::Semireducible);
    expr e1 = replace_rec_apps(ctx, e);
    auto R = elim_match(env, opts, mctx, lctx, e1, elab);

    list<expr> counter_examples;
    if (R.m_counter_examples) {
        unpack_eqns ues(ctx, e);
        counter_examples = map2<expr>(R.m_counter_examples, [&] (list<expr> const & es) {
            return mk_app(ues.get_fn(0), es);
        });
    }

    /* Generate auxiliary definitions */
#ifdef NEW_CODE
    unpack_eqns ues(ctx, e);
    equations_header const & header = get_equations_header(e);
    list<expr> fns             = to_list(R.m_fn); // TODO(Leo): fix after we add support for meta mutual definitions
    list<name> fn_names        = header.m_fn_names;
    list<name> fn_actual_names = header.m_fn_actual_names;
    lean_assert(length(fns) == ues.get_num_fns());
    lean_assert(length(fns) == length(fn_names));
    lean_assert(length(fns) == length(fn_actual_names));
    buffer<expr> new_fns;
    for (unsigned fidx = 0; fidx < ues.get_num_fns(); fidx++) {
        expr fn_type = ctx.infer(ues.get_fn(fidx));
        expr new_fn;
        std::tie(env, new_fn) = mk_aux_definition(env, opts, mctx, lctx, header,
                                                  head(fn_names),
                                                  head(fn_actual_names),
                                                  fn_type, head(fns));
        new_fns.push_back(new_fn);
        fns             = tail(fns);
        fn_names        = tail(fn_names);
        fn_actual_names = tail(fn_actual_names);
    }
    return { to_list(new_fns), counter_examples };
#else
    return { {R.m_fn}, counter_examples };
#endif
}
}
