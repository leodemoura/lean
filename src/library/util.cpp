/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/fresh_name.h"
#include "kernel/find_fn.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/abstract_type_context.h"
#include "kernel/inductive/inductive.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/unfold_macros.h"
#include "library/pp_options.h"
#include "library/projection.h"
#include "library/replace_visitor.h"

namespace lean {
/** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
unsigned get_arity(expr type) {
    unsigned r = 0;
    while (is_pi(type)) {
        type = binding_body(type);
        r++;
    }
    return r;
}

bool is_internal_name(name const & n) {
    return !n.is_anonymous() && n.is_string() && n.get_string() && n.get_string()[0] == '_';
}

level get_level(abstract_type_context & ctx, expr const & A) {
    expr S = ctx.whnf(ctx.infer(A));
    if (!is_sort(S))
        throw exception("invalid expression, sort expected");
    return sort_level(S);
}

bool occurs(expr const & n, expr const & m) {
    return static_cast<bool>(find(m, [&](expr const & e, unsigned) { return n == e; }));
}

bool occurs(name const & n, expr const & m) {
    return static_cast<bool>(find(m, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; }));
}

bool is_app_of(expr const & t, name const & f_name) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name;
}

bool is_app_of(expr const & t, name const & f_name, unsigned nargs) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name && get_app_num_args(t) == nargs;
}

bool is_standard(environment const & env) {
    return env.prop_proof_irrel() && env.impredicative();
}

optional<expr> unfold_term(environment const & env, expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition())
        return none_expr();
    expr d = instantiate_value_univ_params(*decl, const_levels(f));
    buffer<expr> args;
    get_app_rev_args(e, args);
    return some_expr(apply_beta(d, args.size(), args.data()));
}

optional<expr> unfold_app(environment const & env, expr const & e) {
    if (!is_app(e))
        return none_expr();
    return unfold_term(env, e);
}

optional<level> dec_level(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Global: case level_kind::Meta:
        return none_level();
    case level_kind::Succ:
        return some_level(succ_of(l));
    case level_kind::Max:
        if (auto lhs = dec_level(max_lhs(l))) {
        if (auto rhs = dec_level(max_rhs(l))) {
            return some_level(mk_max(*lhs, *rhs));
        }}
        return none_level();
    case level_kind::IMax:
        // Remark: the following mk_max is not a typo. The following
        // assertion justifies it.
        if (auto lhs = dec_level(imax_lhs(l))) {
        if (auto rhs = dec_level(imax_rhs(l))) {
            return some_level(mk_max(*lhs, *rhs));
        }}
        return none_level();
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

/** \brief Return true if environment has a constructor named \c c that returns
    an element of the inductive datatype named \c I, and \c c must have \c nparams parameters. */
bool has_constructor(environment const & env, name const & c, name const & I, unsigned nparams) {
    auto d = env.find(c);
    if (!d || d->is_definition())
        return false;
    expr type = d->get_type();
    unsigned i = 0;
    while (is_pi(type)) {
        i++;
        type = binding_body(type);
    }
    if (i != nparams)
        return false;
    type = get_app_fn(type);
    return is_constant(type) && const_name(type) == I;
}

bool has_poly_unit_decls(environment const & env) {
    return has_constructor(env, get_PolyUnit_star_name(), get_PolyUnit_name(), 0);
}

bool has_eq_decls(environment const & env) {
    return has_constructor(env, get_eq_refl_name(), get_eq_name(), 2);
}

bool has_heq_decls(environment const & env) {
    return has_constructor(env, get_heq_refl_name(), get_heq_name(), 2);
}

bool has_prod_decls(environment const & env) {
    return has_constructor(env, get_Prod_mk_name(), get_Prod_name(), 4);
}

/* n is considered to be recursive if it is an inductive datatype and
   1) It has a constructor that takes n as an argument
   2) It is part of a mutually recursive declaration, and some constructor
      of an inductive datatype takes another inductive datatype from the
      same declaration as an argument. */
bool is_recursive_datatype(environment const & env, name const & n) {
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl) return false;
    for (inductive::intro_rule const & intro : decl->m_intro_rules) {
        expr type = inductive::intro_rule_type(intro);
        while (is_pi(type)) {
            if (find(binding_domain(type), [&](expr const & e, unsigned) {
                        if (is_constant(e)) {
                            name const & c = const_name(e);
                            if (decl->m_name == c) return true;
                        }
                        return false;
                    })) {
                return true;
            }
            type = binding_body(type);
        }
    }
    return false;
}

bool is_reflexive_datatype(abstract_type_context & tc, name const & n) {
    environment const & env = tc.env();
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl) return false;
    for (inductive::intro_rule const & intro : decl->m_intro_rules) {
        expr type = inductive::intro_rule_type(intro);
        while (is_pi(type)) {
            expr arg   = tc.whnf(binding_domain(type));
            if (is_pi(arg) && find(arg, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; })) {
                return true;
            }
            expr local = mk_local(mk_fresh_name(), binding_domain(type));
            type = instantiate(binding_body(type), local);
        }
    }
    return false;
}

level get_datatype_level(expr ind_type) {
    while (is_pi(ind_type))
        ind_type = binding_body(ind_type);
    lean_assert(is_sort(ind_type));
    return sort_level(ind_type);
}

expr update_result_sort(expr t, level const & l) {
    if (is_pi(t)) {
        return update_binding(t, binding_domain(t), update_result_sort(binding_body(t), l));
    } else if (is_sort(t)) {
        return update_sort(t, l);
    } else {
        lean_unreachable();
    }
}

bool is_inductive_predicate(environment const & env, name const & n) {
    if (!is_standard(env))
        return false;
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    return is_zero(get_datatype_level(env.get(n).get_type()));
}

bool can_elim_to_type(environment const & env, name const & n) {
    if (!is_standard(env))
        return true;
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    declaration ind_decl = env.get(n);
    declaration rec_decl = env.get(inductive::get_elim_name(n));
    return rec_decl.get_num_univ_params() > ind_decl.get_num_univ_params();
}

void get_intro_rule_names(environment const & env, name const & n, buffer<name> & result) {
    if (auto decl = inductive::is_inductive_decl(env, n)) {
        for (inductive::intro_rule const & ir : decl->m_intro_rules) {
            result.push_back(inductive::intro_rule_name(ir));
        }
    }
}

optional<name> is_constructor_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn))
        if (auto I = inductive::is_intro_rule(env, const_name(fn)))
            return optional<name>(const_name(fn));
    return optional<name>();
}

optional<name> is_constructor_app_ext(environment const & env, expr const & e) {
    if (auto r = is_constructor_app(env, e))
        return r;
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return optional<name>();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition())
        return optional<name>();
    expr const * it = &decl->get_value();
    while (is_lambda(*it))
        it = &binding_body(*it);
    return is_constructor_app_ext(env, *it);
}

void get_constructor_relevant_fields(environment const & env, name const & n, buffer<bool> & result) {
    lean_assert(inductive::is_intro_rule(env, n));
    expr type        = env.get(n).get_type();
    name I_name      = *inductive::is_intro_rule(env, n);
    unsigned nparams = *inductive::get_num_params(env, I_name);
    buffer<expr> telescope;
    type_checker tc(env);
    to_telescope(tc, type, telescope);
    lean_assert(telescope.size() >= nparams);
    for (unsigned i = nparams; i < telescope.size(); i++) {
        expr ftype = tc.whnf(mlocal_type(telescope[i]));
        result.push_back(!is_sort(ftype) && !tc.is_prop(ftype));
    }
}

unsigned get_constructor_idx(environment const & env, name const & n) {
    lean_assert(inductive::is_intro_rule(env, n));
    name I_name = *inductive::is_intro_rule(env, n);
    buffer<name> cnames;
    get_intro_rule_names(env, I_name, cnames);
    unsigned r  = 0;
    for (name const & cname : cnames) {
        if (cname == n)
            return r;
        r++;
    }
    lean_unreachable();
}

unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n) {
    lean_assert(inductive::is_intro_rule(env, n));
    name I_name = *inductive::is_intro_rule(env, n);
    inductive::inductive_decl decl = *inductive::is_inductive_decl(env, I_name);
    expr type   = env.get(n).get_type();
    unsigned r  = 0;
    while (is_pi(type)) {
        if (find(binding_domain(type), [&](expr const & e, unsigned) {
                    if (is_constant(e)) {
                        name const & c = const_name(e);
                        if (decl.m_name == c)
                            return true;
                    }
                    return false;
                })) {
            r++;
        }
        type = binding_body(type);
    }
    return r;
}

expr instantiate_univ_param (expr const & e, name const & p, level const & l) {
    return instantiate_univ_params(e, to_list(p), to_list(l));
}

unsigned get_expect_num_args(abstract_type_context & ctx, expr e) {
    push_local_fn push_local(ctx);
    unsigned r = 0;
    while (true) {
        e = ctx.whnf(e);
        if (!is_pi(e))
            return r;
        // TODO(Leo): try to avoid the following instantiate.
        expr local = push_local(binding_name(e), binding_domain(e), binding_info(e));
        e = instantiate(binding_body(e), local);
        r++;
    }
}

expr to_telescope(bool pi, expr e, buffer<expr> & telescope,
                  optional<binder_info> const & binfo) {
    while ((pi && is_pi(e)) || (!pi && is_lambda(e))) {
        expr local;
        if (binfo)
            local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), *binfo);
        else
            local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), binding_info(e));
        telescope.push_back(local);
        e = instantiate(binding_body(e), local);
    }
    return e;
}

expr to_telescope(expr const & type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    return to_telescope(true, type, telescope, binfo);
}

expr fun_to_telescope(expr const & e, buffer<expr> & telescope,
                      optional<binder_info> const & binfo) {
    return to_telescope(false, e, telescope, binfo);
}

expr to_telescope(type_checker & ctx, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    expr new_type = ctx.whnf(type);
    while (is_pi(new_type)) {
        type = new_type;
        expr local;
        if (binfo)
            local = mk_local(mk_fresh_name(), binding_name(type), binding_domain(type), *binfo);
        else
            local = mk_local(mk_fresh_name(), binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type     = instantiate(binding_body(type), local);
        new_type = ctx.whnf(type);
    }
    return type;
}

void mk_telescopic_eq(type_checker & tc, buffer<expr> const & t, buffer<expr> const & s, buffer<expr> & eqs) {
    lean_assert(t.size() == s.size());
    lean_assert(std::all_of(s.begin(), s.end(), is_local));
    lean_assert(inductive::has_dep_elim(tc.env(), get_eq_name()));
    buffer<buffer<expr>> t_aux;
    name e_name("e");
    for (unsigned i = 0; i < t.size(); i++) {
        expr s_i = s[i];
        expr s_i_ty   = mlocal_type(s_i);
        expr s_i_ty_a = abstract_locals(s_i_ty, i, s.data());
        expr t_i = t[i];
        t_aux.push_back(buffer<expr>());
        t_aux.back().push_back(t_i);
        for (unsigned j = 0; j < i; j++) {
            if (depends_on(s_i_ty, s[j])) {
                // we need to "cast"
                buffer<expr> ty_inst_args;
                for (unsigned k = 0; k <= j; k++)
                    ty_inst_args.push_back(s[k]);
                for (unsigned k = j + 1; k < i; k++)
                    ty_inst_args.push_back(t_aux[k][j+1]);
                lean_assert(ty_inst_args.size() == i);
                expr s_i_ty = instantiate_rev(s_i_ty_a, i, ty_inst_args.data());
                buffer<expr> rec_args;
                rec_args.push_back(mlocal_type(s[j]));
                rec_args.push_back(t_aux[j][j]);
                rec_args.push_back(Fun(s[j], Fun(eqs[j], s_i_ty))); // type former ("promise")
                rec_args.push_back(t_i); // minor premise
                rec_args.push_back(s[j]);
                rec_args.push_back(eqs[j]);
                level rec_l1 = get_level(tc, s_i_ty);
                level rec_l2 = get_level(tc, mlocal_type(s[j]));
                t_i = mk_app(mk_constant(get_eq_rec_name(), {rec_l1, rec_l2}), rec_args.size(), rec_args.data());
            }
            t_aux.back().push_back(t_i);
        }
        expr eq = mk_local(mk_fresh_name(), e_name.append_after(i+1), mk_eq(tc, t_i, s_i), binder_info());
        eqs.push_back(eq);
    }
}

void mk_telescopic_eq(type_checker & tc, buffer<expr> const & t, buffer<expr> & eqs) {
    lean_assert(std::all_of(t.begin(), t.end(), is_local));
    lean_assert(inductive::has_dep_elim(tc.env(), get_eq_name()));
    buffer<expr> s;
    for (unsigned i = 0; i < t.size(); i++) {
        expr ty = mlocal_type(t[i]);
        ty = abstract_locals(ty, i, t.data());
        ty = instantiate_rev(ty, i, s.data());
        expr local = mk_local(mk_fresh_name(), local_pp_name(t[i]).append_after("'"), ty, local_info(t[i]));
        s.push_back(local);
    }
    return mk_telescopic_eq(tc, t, s, eqs);
}


/* ----------------------------------------------

   Helper functions for creating basic operations

   ---------------------------------------------- */
static expr * g_true = nullptr;
static expr * g_true_intro = nullptr;
static expr * g_and = nullptr;
static expr * g_and_intro = nullptr;
static expr * g_and_elim_left = nullptr;
static expr * g_and_elim_right = nullptr;

expr mk_true() {
    return *g_true;
}

bool is_true(expr const & e) {
    return e == *g_true;
}

expr mk_true_intro() {
    return *g_true_intro;
}

bool is_and(expr const & e, expr & arg1, expr & arg2) {
    if (get_app_fn(e) == *g_and) {
        buffer<expr> args; get_app_args(e, args);
        if (args.size() == 2) {
            arg1 = args[0];
            arg2 = args[1];
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}

bool is_and(expr const & e) {
    if (get_app_fn(e) == *g_and) {
        buffer<expr> args; get_app_args(e, args);
        if (args.size() == 2) return true;
        else return false;
    } else {
        return false;
    }
}

expr mk_and(expr const & a, expr const & b) {
    return mk_app(*g_and, a, b);
}

expr mk_and_intro(abstract_type_context & ctx, expr const & Ha, expr const & Hb) {
    return mk_app(*g_and_intro, ctx.infer(Ha), ctx.infer(Hb), Ha, Hb);
}

expr mk_and_elim_left(abstract_type_context & ctx, expr const & H) {
    expr a_and_b = ctx.whnf(ctx.infer(H));
    return mk_app(*g_and_elim_left, app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_and_elim_right(abstract_type_context & ctx, expr const & H) {
    expr a_and_b = ctx.whnf(ctx.infer(H));
    return mk_app(*g_and_elim_right, app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_unit(level const & l) {
    return mk_constant(get_PolyUnit_name(), {l});
}

expr mk_unit_mk(level const & l) {
    return mk_constant(get_PolyUnit_star_name(), {l});
}

expr mk_prod(abstract_type_context & ctx, expr const & A, expr const & B) {
    level l1 = get_level(ctx, A);
    level l2 = get_level(ctx, B);
    return mk_app(mk_constant(get_Prod_name(), {l1, l2}), A, B);
}

expr mk_pair(abstract_type_context & ctx, expr const & a, expr const & b) {
    expr A = ctx.infer(a);
    expr B = ctx.infer(b);
    level l1 = get_level(ctx, A);
    level l2 = get_level(ctx, B);
    return mk_app(mk_constant(get_Prod_mk_name(), {l1, l2}), A, B, a, b);
}

expr mk_pr1(abstract_type_context & ctx, expr const & p) {
    expr AxB = ctx.whnf(ctx.infer(p));
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_Prod_pr1_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_pr2(abstract_type_context & ctx, expr const & p) {
    expr AxB = ctx.whnf(ctx.infer(p));
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_Prod_pr2_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_nat_zero() {
    return mk_app(mk_constant(get_zero_name(), {mk_level_one()}), {mk_constant(get_Nat_name()), mk_constant(get_zero_nat_name())});
}

expr mk_nat_one() {
    return mk_app(mk_constant(get_one_name(), {mk_level_one()}), {mk_constant(get_Nat_name()), mk_constant(get_one_nat_name())});
}

expr mk_nat_add(expr const & e1, expr const & e2) {
    expr nat_add = mk_app(mk_constant(get_add_name(), {mk_level_one()}), {mk_constant(get_Nat_name()), mk_constant(get_add_nat_name())});
    return mk_app(nat_add, e1, e2);
}

expr mk_unit(level const & l, bool prop) { return prop ? mk_true() : mk_unit(l); }
expr mk_unit_mk(level const & l, bool prop) { return prop ? mk_true_intro() : mk_unit_mk(l); }
expr mk_prod(abstract_type_context & ctx, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and(a, b) : mk_prod(ctx, a, b);
}
expr mk_pair(abstract_type_context & ctx, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and_intro(ctx, a, b) : mk_pair(ctx, a, b);
}
expr mk_pr1(abstract_type_context & ctx, expr const & p, bool prop) {
    return prop ? mk_and_elim_left(ctx, p) : mk_pr1(ctx, p);
}
expr mk_pr2(abstract_type_context & ctx, expr const & p, bool prop) {
    return prop ? mk_and_elim_right(ctx, p) : mk_pr2(ctx, p);
}

bool is_ite(expr const & e, expr & c, expr & H, expr & A, expr & t, expr & f) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn) && const_name(fn) == get_ite_name()) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() == 5) {
            c = args[0]; H = args[1]; A = args[2]; t = args[3]; f = args[4];
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}

bool is_ite(expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn) && const_name(fn) == get_ite_name()) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() == 5) return true;
        else return false;
    } else {
        return false;
    }
}

bool is_iff(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_iff_name();
}
bool is_iff(expr const & e, expr & lhs, expr & rhs) {
    if (!is_iff(e) || !is_app(app_fn(e)))
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}
expr mk_iff(expr const & lhs, expr const & rhs) {
    return mk_app(mk_constant(get_iff_name()), lhs, rhs);
}
expr mk_iff_refl(expr const & a) {
    return mk_app(mk_constant(get_iff_refl_name()), a);
}
expr apply_propext(expr const & iff_pr, expr const & iff_term) {
    lean_assert(is_iff(iff_term));
    return mk_app(mk_constant(get_propext_name()), app_arg(app_fn(iff_term)), app_arg(iff_term), iff_pr);
}

expr mk_eq(abstract_type_context & ctx, expr const & lhs, expr const & rhs) {
    expr A    = ctx.whnf(ctx.infer(lhs));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_name(), {lvl}), A, lhs, rhs);
}

expr mk_eq_refl(abstract_type_context & ctx, expr const & a) {
    expr A    = ctx.whnf(ctx.infer(a));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_refl_name(), {lvl}), A, a);
}

expr mk_eq_symm(abstract_type_context & ctx, expr const & H) {
    expr p    = ctx.whnf(ctx.infer(H));
    lean_assert(is_eq(p));
    expr lhs  = app_arg(app_fn(p));
    expr rhs  = app_arg(p);
    expr A    = ctx.infer(lhs);
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_symm_name(), {lvl}), A, lhs, rhs, H);
}

expr mk_eq_trans(abstract_type_context & ctx, expr const & H1, expr const & H2) {
    expr p1    = ctx.whnf(ctx.infer(H1));
    expr p2    = ctx.whnf(ctx.infer(H2));
    lean_assert(is_eq(p1) && is_eq(p2));
    expr lhs1  = app_arg(app_fn(p1));
    expr rhs1  = app_arg(p1);
    expr rhs2  = app_arg(p2);
    expr A     = ctx.infer(lhs1);
    level lvl  = get_level(ctx, A);
    return mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, lhs1, rhs1, rhs2, H1, H2});
}

expr mk_eq_subst(abstract_type_context & ctx, expr const & motive,
                 expr const & x, expr const & y, expr const & xeqy, expr const & h) {
    expr A    = ctx.infer(x);
    level l1  = get_level(ctx, A);
    expr r;
    if (is_standard(ctx.env())) {
        r = mk_constant(get_eq_subst_name(), {l1});
    } else {
        level l2 = get_level(ctx, ctx.infer(h));
        r = mk_constant(get_eq_subst_name(), {l1, l2});
    }
    return mk_app({r, A, x, y, motive, xeqy, h});
}

expr mk_eq_subst(abstract_type_context & ctx, expr const & motive, expr const & xeqy, expr const & h) {
    expr xeqy_type = ctx.whnf(ctx.infer(xeqy));
    return mk_eq_subst(ctx, motive, app_arg(app_fn(xeqy_type)), app_arg(xeqy_type), xeqy, h);
}

expr mk_congr_arg(abstract_type_context & ctx, expr const & f, expr const & H) {
    expr eq = ctx.relaxed_whnf(ctx.infer(H));
    expr pi = ctx.relaxed_whnf(ctx.infer(f));
    expr A, B, lhs, rhs;
    lean_verify(is_eq(eq, A, lhs, rhs));
    lean_assert(is_arrow(pi));
    B = binding_body(pi);
    level lvl_1  = get_level(ctx, A);
    level lvl_2  = get_level(ctx, B);
    return ::lean::mk_app({mk_constant(get_congr_arg_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, f, H});
}

expr mk_subsingleton_elim(abstract_type_context & ctx, expr const & h, expr const & x, expr const & y) {
    expr A  = ctx.infer(x);
    level l = get_level(ctx, A);
    expr r  = mk_constant(get_subsingleton_elim_name(), {l});
    return mk_app({r, A, h, x, y});
}

expr mk_heq(abstract_type_context & ctx, expr const & lhs, expr const & rhs) {
    expr A    = ctx.whnf(ctx.infer(lhs));
    expr B    = ctx.whnf(ctx.infer(rhs));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_heq_name(), {lvl}), A, lhs, B, rhs);
}

bool is_eq_rec_core(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_eq_rec_name();
}

bool is_eq_rec(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return false;
    return is_standard(env) ? const_name(fn) == get_eq_rec_name() : const_name(fn) == get_eq_nrec_name();
}

bool is_eq_drec(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return false;
    return is_standard(env) ? const_name(fn) == get_eq_drec_name() : const_name(fn) == get_eq_rec_name();
}

bool is_eq(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_eq_name();
}

bool is_eq(expr const & e, expr & lhs, expr & rhs) {
    if (!is_eq(e) || get_app_num_args(e) != 3)
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq(expr const & e, expr & A, expr & lhs, expr & rhs) {
    if (!is_eq(e) || get_app_num_args(e) != 3)
        return false;
    A   = app_arg(app_fn(app_fn(e)));
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq_a_a(expr const & e) {
    if (!is_eq(e))
        return false;
    buffer<expr> args;
    get_app_args(e, args);
    return args.size() == 3 && args[1] == args[2];
}

bool is_eq_a_a(abstract_type_context & ctx, expr const & e) {
    if (!is_eq(e))
        return false;
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() != 3)
        return false;
    return ctx.is_def_eq(args[1], args[2]);
}

bool is_heq(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_heq_name();
}

bool is_heq(expr const & e, expr & A, expr & lhs, expr & B, expr & rhs) {
    if (is_heq(e)) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() != 4)
            return false;
        A = args[0]; lhs = args[1]; B = args[2]; rhs = args[3];
        return true;
    } else {
        return false;
    }
}

expr mk_false() {
    return mk_constant(get_false_name());
}

expr mk_empty() {
    return mk_constant(get_Empty_name());
}

bool is_false(expr const & e) {
    return is_constant(e) && const_name(e) == get_false_name();
}

bool is_empty(expr const & e) {
    return is_constant(e) && const_name(e) == get_Empty_name();
}

expr mk_false_rec(abstract_type_context & ctx, expr const & f, expr const & t) {
    level t_lvl = get_level(ctx, t);
    return mk_app(mk_constant(get_false_rec_name(), {t_lvl}), t, f);
}

bool is_or(expr const & e) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_constant(fn) && const_name(fn) == get_or_name() && args.size() == 2) return true;
    else return false;
}

bool is_or(expr const & e, expr & A, expr & B) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_constant(fn) && const_name(fn) == get_or_name() && args.size() == 2) {
        A = args[0];
        B = args[1];
        return true;
    } else {
        return false;
    }
}

bool is_not(expr const & e, expr & a) {
    if (is_app(e)) {
        expr const & f = app_fn(e);
        if (!is_constant(f) || const_name(f) != get_not_name())
            return false;
        a = app_arg(e);
        return true;
    } else if (is_pi(e)) {
        if (!is_false(binding_body(e)))
            return false;
        a = binding_domain(e);
        return true;
    } else {
        return false;
    }
}

bool is_not(expr const & e) {
    if (is_app(e)) {
        expr const & f = app_fn(e);
        if (!is_constant(f) || const_name(f) != get_not_name())
            return false;
        return true;
    } else if (is_pi(e)) {
        if (!is_false(binding_body(e))) return false;
        return true;
    } else {
        return false;
    }
}

expr mk_not(expr const & e) {
    return mk_app(mk_constant(get_not_name()), e);
}

expr mk_absurd(abstract_type_context & ctx, expr const & t, expr const & e, expr const & not_e) {
    level t_lvl  = get_level(ctx, t);
    expr  e_type = ctx.infer(e);
    return mk_app(mk_constant(get_absurd_name(), {t_lvl}), e_type, t, e, not_e);
}

optional<expr> get_binary_op(expr const & e) {
    if (!is_app(e) || !is_app(app_fn(e)))
        return none_expr();
    return some_expr(app_fn(app_fn(e)));
}

optional<expr> get_binary_op(expr const & e, expr & arg1, expr & arg2) {
    if (auto op = get_binary_op(e)) {
        arg1 = app_arg(app_fn(e));
        arg2 = app_arg(e);
        return some_expr(*op);
    } else {
        return none_expr();
    }
}

expr mk_nary_app(expr const & op, buffer<expr> const & nary_args) {
    return mk_nary_app(op, nary_args.size(), nary_args.data());
}

expr mk_nary_app(expr const & op, unsigned num_nary_args, expr const * nary_args) {
    lean_assert(num_nary_args >= 2);
    // f x1 x2 x3 ==> f x1 (f x2 x3)
    expr e = mk_app(op, nary_args[num_nary_args - 2], nary_args[num_nary_args - 1]);
    for (int i = num_nary_args - 3; i >= 0; --i) {
        e = mk_app(op, nary_args[i], e);
    }
    return e;
}

format pp_type_mismatch(formatter const & fmt, expr const & v, expr const & v_type, expr const & t) {
    format expected_fmt, given_fmt;
    std::tie(expected_fmt, given_fmt) = pp_until_different(fmt, t, v_type);
    format r("type mismatch at term");
    r += pp_indent_expr(fmt, v);
    r += compose(line(), format("has type"));
    r += given_fmt;
    r += compose(line(), format("but is expected to have type"));
    r += expected_fmt;
    return r;
}

expr try_eta(expr const & e) {
    if (is_lambda(e)) {
        expr const & b = binding_body(e);
        if (is_lambda(b)) {
            expr new_b = try_eta(b);
            if (is_eqp(b, new_b)) {
                return e;
            } else if (is_app(new_b) && is_var(app_arg(new_b), 0) && !has_free_var(app_fn(new_b), 0)) {
                return lower_free_vars(app_fn(new_b), 1);
            } else {
                return update_binding(e, binding_domain(e), new_b);
            }
        } else if (is_app(b) && is_var(app_arg(b), 0) && !has_free_var(app_fn(b), 0)) {
            return lower_free_vars(app_fn(b), 1);
        } else {
            return e;
        }
    } else {
        return e;
    }
}

template<bool Eta, bool Beta>
class eta_beta_reduce_fn : public replace_visitor {
public:
    virtual expr visit_app(expr const & e) override {
        expr e1 = replace_visitor::visit_app(e);
        if (Beta && is_head_beta(e1)) {
            return visit(head_beta_reduce(e1));
        } else {
            return e1;
        }
    }

    virtual expr visit_lambda(expr const & e) override {
        expr e1 = replace_visitor::visit_lambda(e);
        if (Eta) {
            while (true) {
                expr e2 = try_eta(e1);
                if (is_eqp(e1, e2))
                    return e1;
                else
                    e1 = e2;
            }
        } else {
            return e1;
        }
    }
};

expr beta_reduce(expr t) {
    return eta_beta_reduce_fn<false, true>()(t);
}

expr eta_reduce(expr t) {
    return eta_beta_reduce_fn<true, false>()(t);
}

expr beta_eta_reduce(expr t) {
    return eta_beta_reduce_fn<true, true>()(t);
}

expr infer_implicit_params(expr const & type, unsigned nparams, implicit_infer_kind k) {
    switch (k) {
    case implicit_infer_kind::Implicit: {
        bool strict = true;
        return infer_implicit(type, nparams, strict);
    }
    case implicit_infer_kind::RelaxedImplicit: {
        bool strict = false;
        return infer_implicit(type, nparams, strict);
    }
    case implicit_infer_kind::None:
        return type;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool get_constructor_rec_args(environment const & env, expr const & e, buffer<pair<expr, unsigned>> & rec_args) {
    type_checker ctx(env);
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (!is_constant(fn)) return false;
    optional<name> I_name = inductive::is_intro_rule(env, const_name(fn));
    if (!I_name) return false;
    expr type       = env.get(const_name(fn)).get_type();
    buffer<expr> tele;
    to_telescope(ctx, type, tele);
    if (tele.size() != args.size()) return false;
    for (unsigned i = 0; i < tele.size(); i++) {
        expr d = tele[i];
        buffer<expr> tele_tele;
        expr r  = to_telescope(ctx, mlocal_type(d), tele_tele);
        expr fn = get_app_fn(r);
        if (is_constant(fn, *I_name)) {
            rec_args.push_back(mk_pair(args[i], tele_tele.size()));
        }
    }
    return true;
}

void initialize_library_util() {
    g_true           = new expr(mk_constant(get_true_name()));
    g_true_intro     = new expr(mk_constant(get_true_intro_name()));
    g_and            = new expr(mk_constant(get_and_name()));
    g_and_intro      = new expr(mk_constant(get_and_intro_name()));
    g_and_elim_left  = new expr(mk_constant(get_and_elim_left_name()));
    g_and_elim_right = new expr(mk_constant(get_and_elim_right_name()));
}

void finalize_library_util() {
    delete g_true;
    delete g_true_intro;
    delete g_and;
    delete g_and_intro;
    delete g_and_elim_left;
    delete g_and_elim_right;
}
}
