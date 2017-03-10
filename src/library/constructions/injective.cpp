/*
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam, Leonardo de Moura
*/
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/declaration.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/constructions/injective.h"
#include "library/type_context.h"
#include "library/app_builder.h"
#include "library/util.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/vm/vm.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/intro_tactic.h"
#include "library/tactic/subst_tactic.h"

namespace lean {

static void collect_args(type_context & tctx, expr const & type, unsigned num_params,
                  buffer<expr> & params, buffer<expr> & args1, buffer<expr> & args2, buffer<expr> & new_args) {
    expr ty = tctx.relaxed_whnf(type);

    for (unsigned param_idx = 0; param_idx < num_params; ++param_idx) {
        expr param = tctx.push_local(binding_name(ty), binding_domain(ty), mk_implicit_binder_info());
        params.push_back(param);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), param));
    }

    expr type_post_params = ty;

    while (is_pi(ty)) {
        expr arg = tctx.push_local(binding_name(ty), binding_domain(ty), mk_implicit_binder_info());
        args1.push_back(arg);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
    }

    expr result_type = ty;
    ty = type_post_params;

    for (expr const & arg1 : args1) {
        if (occurs(arg1, result_type)) {
            args2.push_back(arg1);
        } else {
            expr arg2 = tctx.push_local(binding_name(ty), binding_domain(ty), mk_implicit_binder_info());
            args2.push_back(arg2);
            new_args.push_back(arg2);
        }
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), args2.back()));
    }
    lean_assert(args1.size() == args2.size());
    lean_assert(!is_pi(ty));
}

expr mk_injective_type(environment const & env, name const & ir_name, expr const & ir_type, unsigned num_params, level_param_names const & lp_names) {
    type_context tctx(env);
    buffer<expr> params, args1, args2, new_args;
    collect_args(tctx, ir_type, num_params, params, args1, args2, new_args);
    expr c_ir_params = mk_app(mk_constant(ir_name, param_names_to_levels(lp_names)), params);
    expr lhs = mk_app(c_ir_params, args1);
    expr rhs = mk_app(c_ir_params, args2);
    expr eq_type = mk_eq(tctx, lhs, rhs);

    buffer<expr> eqs;
    for (unsigned arg_idx = 0; arg_idx < args1.size(); ++arg_idx) {
        if (args1[arg_idx] != args2[arg_idx]) {
            if (tctx.is_def_eq(tctx.infer(args1[arg_idx]), tctx.infer(args2[arg_idx]))) {
                eqs.push_back(mk_eq(tctx, args1[arg_idx], args2[arg_idx]));
            } else {
                eqs.push_back(mk_heq(tctx, args1[arg_idx], args2[arg_idx]));
            }
        }
    }

    expr and_type;
    if (eqs.empty()) {
        and_type = mk_true();
    } else {
        and_type = eqs.back();
        unsigned i = eqs.size() - 1;
        while (i > 0) {
            --i;
            and_type = mk_and(eqs[i], and_type);
        }
    }

    return tctx.mk_pi(params, tctx.mk_pi(args1, tctx.mk_pi(new_args, mk_arrow(eq_type, and_type))));
}

expr prove_by_rfl(type_context & tctx, expr const & ty) {
    if (is_heq(ty)) {
        return mk_heq_refl(tctx, app_arg(ty));
    } else {
        return mk_eq_refl(tctx, app_arg(ty));
    }
}

expr prove_conjuncts_by_rfl(type_context & tctx, expr const & ty) {
    expr A, B;
    if (!is_and(ty, A, B)) {
        return prove_by_rfl(tctx, ty);
    } else {
        expr a = prove_by_rfl(tctx, A);
        expr b = prove_conjuncts_by_rfl(tctx, B);
        return mk_app(mk_constant(get_and_intro_name()), {A, B, a, b});
    }
}

expr prove_injective(environment const & env, expr const & inj_type, name const & ind_name) {
    type_context tctx(env);
    expr original_goal_mvar = tctx.mk_metavar_decl(tctx.lctx(), inj_type);
    expr ty = inj_type;

    buffer<expr> args;
    while (is_pi(ty)) {
        expr arg = tctx.push_local_from_binding(ty);
        args.push_back(arg);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
    }

    lean_assert(!args.empty());

    expr tgt = ty;

    if (tgt == mk_true())
        return tctx.mk_lambda(args, mk_true_intro());

    unsigned num_params_indices = *inductive::get_num_params(env, ind_name) + *inductive::get_num_indices(env, ind_name);
    buffer<bool> mask;
    for (unsigned i = 0; i < num_params_indices; ++i) {
        mask.push_back(false);
    }
    mask.push_back(true);
    mask.push_back(false);
    mask.push_back(false);
    mask.push_back(true);

    expr nc_args[] = {tgt, args.back()};
    expr H_nc = mk_app(tctx, name(ind_name, "no_confusion"), num_params_indices + 4, &mask[0], &nc_args[0]);

    // (x1 = x2 -> xs1 == xs2 -> (x1 = x2 /\ xs1 = xs2)
    expr goal_type = binding_domain(tctx.relaxed_whnf(tctx.infer(H_nc)));

    hsubstitution hsubst;
    local_context original_lctx = tctx.lctx();
    expr goal_mvar = tctx.mk_metavar_decl(tctx.lctx(), goal_type);
    tctx.assign(original_goal_mvar, tctx.mk_lambda(args, mk_app(H_nc, goal_mvar)));

    metavar_context mctx = tctx.mctx();
    while (is_pi(mctx.get_metavar_decl(goal_mvar).get_type())) {
        buffer<name> new_Hns;
        expr new_goal_mvar = *intron(env, options(), mctx, goal_mvar, 1, new_Hns);

        local_context new_goal_lctx = mctx.get_metavar_decl(new_goal_mvar).get_context();
        tctx = type_context(env, options(), mctx, new_goal_lctx);

        expr H = tctx.lctx().get_local(new_Hns[0]);

        expr A, B, lhs, rhs;
        if (is_heq(tctx.infer(H), A, lhs, B, rhs)) {
            expr eq_type = mk_eq(tctx, lhs, rhs);
            expr eq_val = mk_eq_of_heq(tctx, H);
            H = tctx.push_let(name("H"), eq_type, eq_val);
            expr next_goal_mvar = tctx.mk_metavar_decl(tctx.lctx(), tctx.infer(new_goal_mvar));
            tctx.assign(new_goal_mvar, next_goal_mvar);
            new_goal_mvar = next_goal_mvar;
        }

        expr H_type = tctx.infer(H);
        lean_assert(is_eq(H_type));

        mctx = tctx.mctx();
        if (app_arg(H_type) != app_arg(app_fn(H_type))) {
            new_goal_mvar = subst(tctx.env(), options(), transparency_mode::None, mctx, new_goal_mvar, H, false, &hsubst);
        }
        goal_mvar = new_goal_mvar;
    }
    tctx = type_context(env, options(), mctx, mctx.get_metavar_decl(goal_mvar).get_context());
    expr pf_of_conjuncts = prove_conjuncts_by_rfl(tctx, tctx.infer(goal_mvar));
    tctx.assign(goal_mvar, pf_of_conjuncts);
    expr pf = tctx.instantiate_mvars(original_goal_mvar);
    return pf;
}

expr prove_injective_arrow(environment const & env, expr const & inj_arrow_type, name const & inj_name) {
    type_context tctx(env);
    expr ty = inj_arrow_type;

    buffer<expr> args;
    while (is_pi(ty)) {
        expr arg = tctx.push_local_from_binding(ty);
        args.push_back(arg);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
    }

    lean_assert(args.size() >= 3);
    expr H_eq = args[args.size() - 3];
    expr H_P = args[args.size() - 2];
    expr H_arrow = args[args.size() - 1];

    expr conjuncts = mk_app(tctx, inj_name, H_eq);
    expr pf = H_arrow;
    while (is_and(tctx.infer(conjuncts))) {
        pf = mk_app(pf, mk_and_elim_left(tctx, conjuncts));
        conjuncts = mk_and_elim_right(tctx, conjuncts);
    }
    pf = mk_app(pf, conjuncts);
    return tctx.mk_lambda(args, pf);
}

environment mk_injective_arrow(environment const & env, name const & ir_name) {
    declaration d = env.get(mk_injective_name(ir_name));
    type_context tctx(env);

    name P_lp_name = mk_fresh_lp_name(d.get_univ_params());
    expr P = tctx.push_local(name("P"), mk_sort(mk_param_univ(P_lp_name)), mk_strict_implicit_binder_info());

    expr ty = d.get_type();
    buffer<expr> args;
    while (is_pi(ty)) {
        expr arg = tctx.push_local_from_binding(ty);
        args.push_back(arg);
        ty = tctx.relaxed_whnf(instantiate(binding_body(ty), arg));
    }

    buffer<expr> eqs;
    expr it = ty;
    expr A, B;
    while (is_and(it, A, B)) {
        eqs.push_back(A);
        it = B;
    }
    eqs.push_back(it);

    expr antecedent = P;
    unsigned i = eqs.size();
    while (i > 0) {
        --i;
        antecedent = mk_arrow(eqs[i], antecedent);
    }

    name inj_arrow_name = mk_injective_arrow_name(ir_name);
    expr inj_arrow_type = tctx.mk_pi(args, tctx.mk_pi(P, mk_arrow(antecedent, P)));
    expr inj_arrow_val = prove_injective_arrow(env, inj_arrow_type, mk_injective_name(ir_name));
    lean_trace(name({"constructions", "injective"}), tout() << inj_arrow_name << " : " << inj_arrow_type << "\n";);
    environment new_env = module::add(env, check(env, mk_definition_inferring_trusted(env, inj_arrow_name,
                                                                                      cons(P_lp_name, d.get_univ_params()), inj_arrow_type, inj_arrow_val, true)));
    return new_env;
}

environment mk_injective_lemmas(environment const & _env, name const & ind_name) {
    environment env = _env;

    auto idecls = inductive::is_inductive_decl(env, ind_name);
    if (!idecls)
        throw exception(sstream() << "'" << ind_name << "' not an inductive datatype\n");

    if (is_inductive_predicate(env, ind_name) || !can_elim_to_type(env, ind_name))
        return _env;

    inductive::inductive_decl idecl = *idecls;
    level_param_names lp_names = idecl.m_level_params;
    unsigned num_params = idecl.m_num_params;

    buffer<inductive::intro_rule> intro_rules;
    to_buffer(idecl.m_intro_rules, intro_rules);

    for (inductive::intro_rule ir : intro_rules) {
        name ir_name = inductive::intro_rule_name(ir);
        expr ir_type = inductive::intro_rule_type(ir);
        expr inj_type = mk_injective_type(env, ir_name, ir_type, num_params, lp_names);
        expr inj_val = prove_injective(env, inj_type, ind_name);
        lean_trace(name({"constructions", "injective"}), tout() << ir_name << " : " << inj_type << " :=\n  " << inj_val;);
        env = module::add(env, check(env, mk_definition_inferring_trusted(env, mk_injective_name(ir_name), lp_names, inj_type, inj_val, true)));
        env = mk_injective_arrow(env, ir_name);
    }
    return env;
}

name mk_injective_name(name const & ir_name) {
    return name(ir_name, "inj");
}

name mk_injective_arrow_name(name const & ir_name) {
    return name(ir_name, "inj_arrow");
}

void initialize_injective() {
    register_trace_class(name({"constructions", "injective"}));
}

void finalize_injective() {}
}
