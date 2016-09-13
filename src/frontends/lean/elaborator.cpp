/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/find_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/user_recursors.h"
#include "library/aux_recursors.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/scope_pos_info_provider.h"
#include "library/choice.h"
#include "library/util.h"
#include "library/typed_expr.h"
#include "library/annotation.h"
#include "library/pp_options.h"
#include "library/flycheck.h"
#include "library/replace_visitor.h"
#include "library/error_handling.h"
#include "library/locals.h"
#include "library/private.h"
#include "library/attribute_manager.h"
#include "library/vm/vm.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/kabstract.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/elaborate.h"
#include "library/equations_compiler/compiler.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/util.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/info_annotation.h"

namespace lean {
MK_THREAD_LOCAL_GET(type_context_cache_manager, get_tcm, true /* use binder information at infer_cache */);

static name * g_level_prefix = nullptr;
static name * g_elab_with_expected_type = nullptr;
static name * g_elab_as_eliminator = nullptr;

#define trace_elab(CODE) lean_trace("elaborator", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_detail(CODE) lean_trace("elaborator_detail", scope_trace_env _scope(m_env, m_ctx); CODE)
#define trace_elab_debug(CODE) lean_trace("elaborator_debug", scope_trace_env _scope(m_env, m_ctx); CODE)

bool elab_with_expected_type(environment const & env, name const & d) {
    return has_attribute(env, *g_elab_with_expected_type, d);
}

bool elab_as_eliminator(environment const & env, name const & d) {
    return has_attribute(env, *g_elab_as_eliminator, d);
}

elaborator::elaborator(environment const & env, options const & opts, metavar_context const & mctx,
                       local_context const & lctx):
    m_env(env), m_opts(opts),
    m_ctx(env, opts, mctx, lctx, get_tcm(), transparency_mode::Semireducible) {
}

auto elaborator::mk_pp_ctx() -> pp_fn {
    return ::lean::mk_pp_ctx(m_ctx.env(), m_opts, m_ctx.mctx(), m_ctx.lctx());
}

format elaborator::pp_indent(pp_fn const & pp_fn, expr const & e) {
    unsigned i = get_pp_indent(m_opts);
    return nest(i, line() + pp_fn(e));
}

format elaborator::pp_indent(expr const & e) {
    return pp_indent(mk_pp_ctx(), e);
}

format elaborator::pp_overloads(pp_fn const & pp_fn, buffer<expr> const & fns) {
    format r("overloads:");
    r += space();
    bool first = true;
    for (expr const & fn : fns) {
        if (first) first = false; else r += format(", ");
        r += pp_fn(fn);
    }
    return paren(r);
}

static std::string pos_string_for(expr const & e) {
    pos_info_provider * provider = get_pos_info_provider();
    if (!provider) return "'unknown'";
    pos_info pos  = provider->get_pos_info_or_some(e);
    sstream s;
    s << provider->get_file_name() << ":" << pos.first << ":" << pos.second << ":";
    return s.str();
}

level elaborator::mk_univ_metavar() {
    level r = m_ctx.mk_univ_metavar_decl();
    m_uvar_stack = cons(r, m_uvar_stack);
    return r;
}

expr elaborator::mk_metavar(expr const & A) {
    expr r = copy_tag(A, m_ctx.mk_metavar_decl(m_ctx.lctx(), A));
    m_mvar_stack = cons(r, m_mvar_stack);
    return r;
}

expr elaborator::mk_metavar(optional<expr> const & A) {
    if (A)
        return mk_metavar(*A);
    else
        return mk_metavar(mk_type_metavar());
}

expr elaborator::mk_type_metavar() {
    level l = mk_univ_metavar();
    return mk_metavar(mk_sort(l));
}

expr elaborator::mk_instance_core(local_context const & lctx, expr const & C, expr const & ref) {
    optional<expr> inst = m_ctx.mk_class_instance_at(lctx, C);
    if (!inst) {
        metavar_context mctx   = m_ctx.mctx();
        local_context new_lctx = lctx.instantiate_mvars(mctx);
        tactic_state s = ::lean::mk_tactic_state_for(m_env, m_opts, mctx, new_lctx, C);
        throw elaborator_exception(ref, format("failed to synthesize type class instance for") + line() + s.pp());
    }
    return *inst;
}

expr elaborator::mk_instance_core(expr const & C, expr const & ref) {
    return mk_instance_core(m_ctx.lctx(), C, ref);
}

expr elaborator::mk_instance(expr const & C, expr const & ref) {
    if (has_expr_metavar(C)) {
        expr inst = copy_tag(ref, mk_metavar(C));
        m_instance_stack = cons(inst, m_instance_stack);
        return inst;
    } else {
        return mk_instance_core(C, ref);
    }
}

expr elaborator::instantiate_mvars(expr const & e) {
    expr r = m_ctx.instantiate_mvars(e);
    if (r.get_tag() == nulltag)
        r.set_tag(e.get_tag());
    return r;
}

level elaborator::get_level(expr const & A, expr const & ref) {
    expr A_type = whnf(infer_type(A));
    if (is_sort(A_type)) {
        return sort_level(A_type);
    }

    if (is_meta(A_type)) {
        checkpoint C(*this);
        level l = mk_univ_metavar();
        if (is_def_eq(A_type, mk_sort(l))) {
            C.commit();
            return l;
        }
    }

    auto pp_fn = mk_pp_ctx();
    throw elaborator_exception(ref, format("type expected at") + pp_indent(pp_fn, A));
}

level elaborator::replace_univ_placeholder(level const & l) {
    auto fn = [&](level const & l) {
        if (is_placeholder(l))
            return some_level(mk_univ_metavar());
        else
            return none_level();
    };
    return replace(l, fn);
}

static bool contains_placeholder(level const & l) {
    bool contains = false;
    auto fn = [&](level const & l) {
        if (contains) return false;
        if (is_placeholder(l))
            contains = true;
        return true;
    };
    for_each(l, fn);
    return contains;
}

/* Here, we say a term is first-order IF all applications are of the form (f ...) where f is a constant. */
static bool is_first_order(expr const & e) {
    return !find(e, [&](expr const & e, unsigned) {
            return is_app(e) && !is_constant(get_app_fn(e));
        });
}

bool elaborator::is_elim_elab_candidate(name const & fn) {
    if (inductive::is_elim_rule(m_env, fn))
        return true;
    if (is_aux_recursor(m_env, fn))
        return true;
    if (is_user_defined_recursor(m_env, fn))
        return true;
    if (elab_as_eliminator(m_env, fn))
        return true;
    return false;
}

/** See comment at elim_info */
auto elaborator::get_elim_info_for_builtin(name const & fn) -> elim_info {
    lean_assert(is_aux_recursor(m_env, fn) || inductive::is_elim_rule(m_env, fn));
    /* Remark: this is not just an optimization. The code at use_elim_elab_core
       only works for dependent elimination. */
    lean_assert(!fn.is_atomic());
    name const & I_name    = fn.get_prefix();
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(m_env, I_name);
    lean_assert(decl);
    unsigned nparams  = decl->m_num_params;
    unsigned nindices = *inductive::get_num_indices(m_env, I_name);
    unsigned nminors  = length(decl->m_intro_rules);
    elim_info r;
    if (strcmp(fn.get_string(), "brec_on") == 0 || strcmp(fn.get_string(), "binduction_on") == 0) {
        r.m_arity      = nparams + 1 /* motive */ + nindices + 1 /* major */ + 1;
    } else {
        r.m_arity      = nparams + 1 /* motive */ + nindices + 1 /* major */ + nminors;
    }
    r.m_nexplicit  = 1 /* major premise */ + nminors;
    r.m_motive_idx = nparams;
    unsigned major_idx;
    if (inductive::is_elim_rule(m_env, fn)) {
        major_idx = nparams + 1 + nindices + nminors;
    } else {
        major_idx = nparams + 1 + nindices;
    }
    r.m_idxs = to_list(major_idx);
    return r;
}

/** See comment at elim_info */
auto elaborator::use_elim_elab_core(name const & fn) -> optional<elim_info> {
    if (!is_elim_elab_candidate(fn))
        return optional<elim_info>();
    // if (is_aux_recursor(m_env, fn) || inductive::is_elim_rule(m_env, fn)) {
    // return optional<elim_info>(get_elim_info_for_builtin(fn));
    // }
    type_context::tmp_locals locals(m_ctx);
    declaration d     = m_env.get(fn);
    expr type         = d.get_type();
    while (is_pi(type)) {
        type = instantiate(binding_body(type), locals.push_local_from_binding(type));
    }

    buffer<expr> C_args;
    expr const & C = get_app_args(type, C_args);
    if (!is_local(C) || C_args.empty() || !std::all_of(C_args.begin(), C_args.end(), is_local)) {
        trace_elab_detail(tout() << "'eliminator' elaboration is not used for '" << fn <<
                          "' because resulting type is not of the expected form\n";);
        return optional<elim_info>();
    }

    buffer<expr> const & params = locals.as_buffer();
    optional<unsigned> _midx = params.index_of(C);
    if (!_midx)
        return optional<elim_info>();

    unsigned midx = *_midx;
    buffer<unsigned> idxs;
    buffer<bool>     found;
    found.resize(C_args.size(), false);
    unsigned i    = params.size();
    unsigned nexplicit = 0;
    while (i > 0) {
        --i;
        expr const & param = params[i];

        if (!is_explicit(local_info(param))) {
            continue;
        }
        nexplicit++;

        if (optional<unsigned> pos = C_args.index_of(param)) {
            // Parameter is an argument of the resulting type (C ...)
            if (!found[*pos]) {
                // We store it if we could not infer it using the type of other arguments.
                found[*pos] = true;
                idxs.push_back(i);
            }
            continue;
        }

        expr param_type = m_ctx.infer(param);
        if (!is_first_order(param_type))
            continue;

        bool collected = false;
        for_each(param_type, [&](expr const & e, unsigned) {
                if (is_local(e)) {
                    if (optional<unsigned> pos = C_args.index_of(e)) {
                        if (!found[*pos]) {
                            collected   = true;
                            found[*pos] = true;
                        }
                    }
                }
                return true;
            });
        if (collected)
            idxs.push_back(i);
    }

    for (unsigned i = 0; i < found.size(); i++) {
        if (!found[i]) {
            trace_elab_detail(tout() << "'eliminator' elaboration is not used for '" << fn <<
                              "' because did not find a (reliable) way to synthesize '" << C_args[i] << "' " <<
                              "which occurs in the resulting type\n";);
            return optional<elim_info>();
        }
    }

    std::reverse(idxs.begin(), idxs.end());
    trace_elab_detail(tout() << "'eliminator' elaboration is going to be used for '" << fn << "' applications, "
                      << "the motive is computed using the argument(s):";
                      for (unsigned idx : idxs) tout() << " #" << (idx+1);
                      tout() << "\n";);
    return optional<elim_info>(params.size(), nexplicit, midx, to_list(idxs));
}

/** See comment at elim_info */
auto elaborator::use_elim_elab(name const & fn) -> optional<elim_info> {
    if (auto it = m_elim_cache.find(fn))
        return *it;
    optional<elim_info> r = use_elim_elab_core(fn);
    m_elim_cache.insert(fn, r);
    return r;
}

void elaborator::trace_coercion_failure(expr const & e_type, expr const & type, expr const & ref, char const * error_msg) {
    trace_elab({
            auto pp_fn = mk_pp_ctx();
            format msg("coercion at ");
            msg += format(pos_string_for(ref));
            msg += space() + format("from");
            msg += pp_indent(pp_fn, e_type);
            msg += line() + format("to");
            msg += pp_indent(pp_fn, type);
            msg += line() + format(error_msg);
            tout() << msg << "\n";
        });
}

optional<expr> elaborator::mk_coercion(expr const & e, expr const & _e_type, expr const & _type, expr const & ref) {
    expr e_type = instantiate_mvars(_e_type);
    expr type   = instantiate_mvars(_type);
    if (!has_expr_metavar(e_type) && !has_expr_metavar(type)) {
        expr has_coe_t;
        try {
            has_coe_t = mk_app(m_ctx, get_has_coe_t_name(), e_type, type);
        } catch (app_builder_exception & ex) {
            trace_coercion_failure(e_type, type, ref,
                                   "failed create type class expression 'has_coe_t' "
                                   "('set_option trace.app_builder true' for more information)");
            return none_expr();
        }
        optional<expr> inst = m_ctx.mk_class_instance_at(m_ctx.lctx(), has_coe_t);
        if (!inst) {
            trace_coercion_failure(e_type, type, ref,
                                   "failed to synthesize 'has_coe_t' type class instance "
                                   "('set_option trace.class_instances true' for more information)");
            return none_expr();
        }
        expr coe_to_lift;
        try {
            coe_to_lift = mk_app(m_ctx, get_coe_to_lift_name(), *inst);
        } catch (app_builder_exception & ex) {
            trace_coercion_failure(e_type, type, ref,
                                   "failed convert 'has_coe_t' instance into 'has_lift_t' instance "
                                   "('set_option trace.app_builder true' for more information)");
            return none_expr();
        }
        expr coe;
        try {
            coe = mk_app(m_ctx, get_coe_name(), coe_to_lift, e);
        } catch (app_builder_exception & ex) {
            trace_coercion_failure(e_type, type, ref,
                                   "failed create 'coe' application using generated type class instance "
                                   "('set_option trace.app_builder true' for more information)");
            return none_expr();
        }
        return some_expr(coe);
    } else {
        trace_coercion_failure(e_type, type, ref,
                               "was not considered because types contain metavariables");
        return none_expr();
    }
}

optional<expr> elaborator::ensure_has_type(expr const & e, expr const & e_type, expr const & type, expr const & ref) {
    type_context::approximate_scope scope(m_ctx);

    if (is_def_eq(e_type, type))
        return some_expr(e);

    return mk_coercion(e, e_type, type, ref);
}

expr elaborator::enforce_type(expr const & e, expr const & expected_type, char const * header, expr const & ref) {
    expr e_type = infer_type(e);
    if (auto r = ensure_has_type(e, e_type, expected_type, ref)) {
        return *r;
    } else {
        format msg = format(header);
        auto pp_fn = mk_pp_ctx();
        msg += format(", expression") + pp_indent(pp_fn, e);
        msg += line() + format("has type") + pp_indent(pp_fn, e_type);
        msg += line() + format("but is expected to have type") + pp_indent(pp_fn, expected_type);
        throw elaborator_exception(ref, msg);
    }
}

void elaborator::trace_coercion_fn_sort_failure(bool is_fn, expr const & e_type, expr const & ref, char const * error_msg) {
    trace_elab({
            format msg("coercion at ");
            auto pp_fn = mk_pp_ctx();
            msg += format(pos_string_for(ref));
            msg += space() + format("from");
            msg += pp_indent(pp_fn, e_type);
            if (is_fn)
                msg += line() + format("to function space");
            else
                msg += line() + format("to sort");
            msg += line() + format(error_msg);
            tout() << msg << "\n";
        });
}

optional<expr> elaborator::mk_coercion_to_fn_sort(bool is_fn, expr const & e, expr const & _e_type, expr const & ref) {
    expr e_type = instantiate_mvars(_e_type);
    if (!has_expr_metavar(e_type)) {
        try {
            bool mask[3] = { true, false, true };
            expr args[2] = { e_type, e };
            expr new_e = mk_app(m_ctx, is_fn ? get_coe_fn_name() : get_coe_sort_name(), 3, mask, args);
            expr new_e_type = whnf(infer_type(new_e));
            if ((is_fn && is_pi(new_e_type)) || (!is_fn && is_sort(new_e_type))) {
                return some_expr(new_e);
            }
            trace_coercion_fn_sort_failure(is_fn, e_type, ref,
                                           "coercion was successfully generated, but resulting type is not the expected one");
            return none_expr();
        } catch (app_builder_exception & ex) {
            trace_coercion_fn_sort_failure(is_fn, e_type, ref,
                                           "failed create coercion application using type class resolution "
                                           "('set_option trace.app_builder true' and 'set_option trace.class_instances true' for more information)");
            return none_expr();
        }
    } else {
        trace_coercion_fn_sort_failure(is_fn, e_type, ref,
                                       "was not considered because type contain metavariables");
        return none_expr();
    }
}

expr elaborator::ensure_function(expr const & e, expr const & ref) {
    expr e_type = whnf(infer_type(e));
    if (is_pi(e_type)) {
        return e;
    }
    if (auto r = mk_coercion_to_fn(e, e_type, ref)) {
        return *r;
    }
    auto pp_fn = mk_pp_ctx();
    throw elaborator_exception(ref, format("function expected at") + pp_indent(pp_fn, e));
}

expr elaborator::ensure_type(expr const & e, expr const & ref) {
    expr e_type = whnf(infer_type(e));
    if (is_sort(e_type)) {
        return e;
    }

    if (is_meta(e_type)) {
        checkpoint C(*this);
        if (is_def_eq(e_type, mk_sort(mk_univ_metavar()))) {
            C.commit();
            return e;
        }
    }

    if (auto r = mk_coercion_to_sort(e, e_type, ref)) {
        return *r;
    }

    auto pp_fn = mk_pp_ctx();
    throw elaborator_exception(ref, format("type expected at") + pp_indent(pp_fn, e));
}

expr elaborator::visit_typed_expr(expr const & e) {
    expr ref          = e;
    expr val          = get_typed_expr_expr(e);
    expr type         = get_typed_expr_type(e);
    expr new_type;
    {
        checkpoint C(*this);
        new_type = ensure_type(visit(type, none_expr()), type);
        process_checkpoint(C);
    }
    expr new_val      = visit(val, some_expr(new_type));
    expr new_val_type = infer_type(new_val);
    if (auto r = ensure_has_type(new_val, new_val_type, new_type, ref))
        return *r;

    auto pp_fn = mk_pp_ctx();
    throw elaborator_exception(ref,
                               format("invalid type ascription, expression has type") + pp_indent(pp_fn, new_val_type) +
                               line() + format("but is expected to have type") + pp_indent(pp_fn, new_type));
}

expr elaborator::visit_prenum(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_prenum(e));
    expr ref = e;
    mpz const & v  = prenum_value(e);
    tag e_tag      = e.get_tag();
    expr A;
    if (expected_type) {
        A = *expected_type;
        if (is_metavar(*expected_type))
            m_numeral_type_stack = cons(A, m_numeral_type_stack);
    } else {
        A = mk_type_metavar();
        m_numeral_type_stack = cons(A, m_numeral_type_stack);
    }
    level A_lvl = get_level(A, ref);
    levels ls(A_lvl);
    if (v.is_neg())
        throw elaborator_exception(ref, "invalid pre-numeral, it must be a non-negative value");
    if (v.is_zero()) {
        expr has_zero_A = mk_app(mk_constant(get_has_zero_name(), ls), A, e_tag);
        expr S          = mk_instance(has_zero_A, ref);
        return mk_app(mk_app(mk_constant(get_zero_name(), ls), A, e_tag), S, e_tag);
    } else {
        expr has_one_A = mk_app(mk_constant(get_has_one_name(), ls), A, e_tag);
        expr S_one     = mk_instance(has_one_A, ref);
        expr one       = mk_app(mk_app(mk_constant(get_one_name(), ls), A, e_tag), S_one, e_tag);
        if (v == 1) {
            return one;
        } else {
            expr has_add_A = mk_app(mk_constant(get_has_add_name(), ls), A, e_tag);
            expr S_add     = mk_instance(has_add_A, ref);
            std::function<expr(mpz const & v)> convert = [&](mpz const & v) {
                lean_assert(v > 0);
                if (v == 1)
                    return one;
                else if (v % mpz(2) == 0) {
                    expr r = convert(v / 2);
                    return mk_app(mk_app(mk_app(mk_constant(get_bit0_name(), ls), A, e_tag), S_add, e_tag), r, e_tag);
                } else {
                    expr r = convert(v / 2);
                    return mk_app(mk_app(mk_app(mk_app(mk_constant(get_bit1_name(), ls), A, e_tag), S_one, e_tag),
                                         S_add, e_tag), r, e_tag);
                }
            };
            return convert(v);
        }
    }
}

expr elaborator::visit_sort(expr const & e) {
    level new_l = replace_univ_placeholder(sort_level(e));
    expr r = update_sort(e, new_l);
    if (contains_placeholder(sort_level(e)))
        m_to_check_sorts.emplace_back(e, r);
    return r;
}

expr elaborator::visit_const_core(expr const & e) {
    declaration d = m_env.get(const_name(e));
    buffer<level> ls;
    for (level const & l : const_levels(e)) {
        level new_l = replace_univ_placeholder(l);
        ls.push_back(new_l);
    }
    unsigned num_univ_params = d.get_num_univ_params();
    if (num_univ_params < ls.size()) {
        format msg("incorrect number of universe levels parameters for '");
        msg += format(const_name(e)) + format("', #") + format(num_univ_params);
        msg += format(" expected, #") + format(ls.size()) + format("provided");
        throw elaborator_exception(e, msg);
    }
    // "fill" with meta universe parameters
    for (unsigned i = ls.size(); i < num_univ_params; i++)
        ls.push_back(mk_univ_metavar());
    lean_assert(num_univ_params == ls.size());
    return update_constant(e, to_list(ls.begin(), ls.end()));
}

expr elaborator::visit_function(expr const & fn, bool has_args, expr const & ref) {
    if (is_placeholder(fn)) {
        throw elaborator_exception(ref, "placeholders '_' cannot be used where a function is expected");
    }
    expr r;
    switch (fn.kind()) {
    case expr_kind::Var:
    case expr_kind::Pi:
    case expr_kind::Meta:
    case expr_kind::Sort:
        throw elaborator_exception(ref, "invalid application, function expected");
    // The expr_kind::App case can only happen when nary notation is used
    case expr_kind::App:       r = visit(fn, none_expr()); break;
    case expr_kind::Local:     r = fn; break;
    case expr_kind::Constant:  r = visit_const_core(fn); break;
    case expr_kind::Macro:     r = visit_macro(fn, none_expr(), true); break;
    case expr_kind::Lambda:    r = visit_lambda(fn, none_expr()); break;
    case expr_kind::Let:       r = visit_let(fn, none_expr()); break;
    }
    if (has_args)
        r = ensure_function(r, ref);
    return r;
}

void elaborator::validate_overloads(buffer<expr> const & fns, expr const & ref) {
    for (expr const & fn_i : fns) {
        if (is_constant(fn_i) && use_elim_elab(const_name(fn_i))) {
            auto pp_fn = mk_pp_ctx();
            format msg("invalid overloaded application, "
                       "elaborator has special support for '");
            msg += pp_fn(fn_i);
            msg += format("' (it is handled as an \"eliminator\"), "
                          "but this kind of constant cannot be overloaded "
                          "(solution: use fully qualified names) ");
            msg += pp_overloads(pp_fn, fns);
            return throw elaborator_exception(ref, msg);
        }
    }
}

format elaborator::mk_app_type_mismatch_error(expr const & t, expr const & arg, expr const & arg_type,
                                              expr const & expected_type) {
    auto pp_fn = mk_pp_ctx();
    format msg = format("type mismatch at application");
    msg += pp_indent(pp_fn, t);
    msg += line() + format("term");
    msg += pp_indent(pp_fn, arg);
    msg += line() + format("has type");
    msg += pp_indent(pp_fn, arg_type);
    msg += line() + format("but is expected to have type");
    msg += pp_indent(pp_fn, expected_type);
    return msg;
}

format elaborator::mk_too_many_args_error(expr const & fn_type) {
    auto pp_fn = mk_pp_ctx();
    return
        format("invalid function application, too many arguments, function type:") +
        pp_indent(pp_fn, fn_type);
}

void elaborator::throw_app_type_mismatch(expr const & t, expr const & arg, expr const & arg_type, expr const & expected_type,
                                         expr const & ref) {
    throw elaborator_exception(ref, mk_app_type_mismatch_error(t, arg, arg_type, expected_type));
}

expr elaborator::visit_elim_app(expr const & fn, elim_info const & info, buffer<expr> const & args,
                                optional<expr> const & _expected_type, expr const & ref) {
    trace_elab_detail(tout() << "recursor/eliminator application at " << pos_string_for(ref) << "\n";);
    lean_assert(info.m_nexplicit <= args.size());
    if (!_expected_type) {
        throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) + format ("' application, ") +
                                   format("elaborator has special support for this kind of application ") +
                                   format("(it is handled as an \"eliminator\"), ") +
                                   format("but the expected type must be known"));
    }

    expr expected_type = instantiate_mvars(*_expected_type);
    if (has_expr_metavar(expected_type)) {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) + format ("' application, ") +
                                   format("elaborator has special support for this kind of application ") +
                                   format("(it is handled as an \"eliminator\"), ") +
                                   format("but expected type must not contain metavariables") +
                                   pp_indent(pp_fn, expected_type));
    }

    trace_elab_debug(
        tout() << "eliminator elaboration for '" << fn << "'\n"
        << "  arity:     " << info.m_arity << "\n"
        << "  nexplicit: " << info.m_nexplicit << "\n"
        << "  motive:    #" << (info.m_motive_idx+1) << "\n"
        << "  \"major\":  ";
        for (unsigned idx : info.m_idxs)
            tout() << " #" << (idx+1);
        tout() << "\n";);

    expr fn_type = try_to_pi(infer_type(fn));
    buffer<expr> new_args;

    /* In the first pass we only process the arguments at info.m_idxs */
    expr type = fn_type;
    unsigned i = 0;
    unsigned j = 0;
    list<unsigned> main_idxs  = info.m_idxs;
    buffer<optional<expr>> postponed_args; // mark arguments that must be elaborated in the second pass.
    {
        while (is_pi(type)) {
            expr const & d = binding_domain(type);
            binder_info const & bi = binding_info(type);
            expr new_arg;
            optional<expr> postponed;
            if (std::find(main_idxs.begin(), main_idxs.end(), i) != main_idxs.end()) {
                {
                    checkpoint C(*this);
                    new_arg = visit(args[j], some_expr(d));
                    process_checkpoint(C);
                    new_arg = instantiate_mvars(new_arg);
                }
                j++;
                if (has_expr_metavar(new_arg)) {
                    auto pp_fn = mk_pp_ctx();
                    throw elaborator_exception(ref, format("invalid '") + format(const_name(fn)) +
                                               format ("' application, ") +
                                               format("elaborator has special support for this kind of application ") +
                                               format("(it is handled as an \"eliminator\"), ") +
                                               format("but term") + pp_indent(pp_fn, new_arg) +
                                               line() + format("must not contain metavariables because") +
                                               format(" it is used to compute the motive"));
                }
                expr new_arg_type = infer_type(new_arg);
                if (!is_def_eq(new_arg_type, d)) {
                    throw elaborator_exception(ref, mk_app_type_mismatch_error(mk_app(fn, i+1, new_args.data()),
                                                                               new_arg, new_arg_type, d));
                }
            } else if (is_explicit(bi)) {
                new_arg   = mk_metavar(d);
                postponed = args[j];
                j++;
            } else if (bi.is_inst_implicit()) {
                new_arg = mk_instance(d, ref);
            } else {
                new_arg = mk_metavar(d);
            }
            new_args.push_back(new_arg);
            postponed_args.push_back(postponed);
            type = try_to_pi(instantiate(binding_body(type), new_arg));
            i++;
        }

        lean_assert(new_args.size() == info.m_arity);

        {
            /* Process extra arguments */
            checkpoint C(*this);
            for (; j < args.size(); j++) {
                new_args.push_back(visit(args[j], none_expr()));
            }
            process_checkpoint(C);
        }
    }

    /* Compute expected_type for the recursor application without extra arguments */
    buffer<expr> extra_args;
    i = new_args.size();
    while (i > info.m_arity) {
        --i;
        expr new_arg      = instantiate_mvars(new_args[i]);
        expr new_arg_type = instantiate_mvars(infer_type(new_arg));
        expected_type     = ::lean::mk_pi("_a", new_arg_type, kabstract(m_ctx, expected_type, new_arg));
        extra_args.push_back(new_arg);
    }
    new_args.shrink(i);
    std::reverse(extra_args.begin(), extra_args.end());

    // Compute motive */
    trace_elab_debug(tout() << "compute motive by using keyed-abstraction:\n  " <<
                     instantiate_mvars(type) << "\nwith\n  " <<
                     expected_type << "\n";);
    expr motive = expected_type;
    buffer<expr> keys;
    get_app_args(type, keys);
    i = keys.size();
    while (i > 0) {
        --i;
        expr k = instantiate_mvars(keys[i]);
        expr k_type    = infer_type(k);
        motive = ::lean::mk_lambda("_x", k_type, kabstract(m_ctx, motive, k));
    }
    trace_elab_debug(tout() << "motive:\n  " << instantiate_mvars(motive) << "\n";);

    expr motive_arg = new_args[info.m_motive_idx];
    if (!is_def_eq(motive_arg, motive)) {
        throw elaborator_exception(ref, "\"eliminator\" elaborator failed to compute the motive");
    }

    /* Elaborate postponed arguments */
    for (unsigned i = 0; i < new_args.size(); i++) {
        if (optional<expr> arg = postponed_args[i]) {
            lean_assert(is_metavar(new_args[i]));
            expr new_arg_type = instantiate_mvars(infer_type(new_args[i]));
            expr new_arg      = visit(*arg, some_expr(new_arg_type));
            if (!is_def_eq(new_args[i], new_arg)) {
                auto pp_fn = mk_pp_ctx();
                throw elaborator_exception(ref, format("\"eliminator\" elaborator type mismatch, term") +
                                           pp_indent(pp_fn, new_arg) +
                                           line() + format("has type") +
                                           pp_indent(pp_fn, infer_type(new_arg)) +
                                           line() + format("but is expected to have type") +
                                           pp_indent(pp_fn, new_arg_type));
            } else {
                new_args[i] = new_arg;
            }
        }
    }

    expr r = instantiate_mvars(mk_app(mk_app(fn, new_args), extra_args));
    trace_elab_debug(tout() << "elaborated recursor:\n  " << r << "\n";);
    return r;
}

optional<expr> elaborator::visit_app_with_expected(expr const & fn, buffer<expr> const & args,
                                                   expr const & expected_type, expr const & ref) {
    snapshot C(*this);
    buffer<expr> new_args;
    buffer<expr> args_mvars;
    buffer<expr> args_expected_types;
    /* size_at_args[i] contains size of new_args after args_mvars[i] was pushed.
       We need this information for producing error messages. */
    buffer<unsigned> size_at_args;
    expr fn_type          = infer_type(fn);
    expr type_before_whnf = fn_type;
    expr type             = whnf(fn_type);
    buffer<expr> new_instances;
    unsigned i   = 0;
    /* First pass: compute type for an fn-application, and unify it with expected_type.
       We don't visit expelicit arguments at this point. */
    while (is_pi(type)) {
        binder_info const & bi = binding_info(type);
        expr const & d = binding_domain(type);
        if (bi.is_strict_implicit() && i == args.size())
            break;
        expr new_arg;
        if (!is_explicit(bi)) {
            // implicit argument
            new_arg = mk_metavar(d);
            if (bi.is_inst_implicit())
                new_instances.push_back(new_arg);
            // implicit arguments are tagged as inaccessible in patterns
            if (m_in_pattern)
                new_arg = copy_tag(ref, mk_inaccessible(new_arg));
        } else if (i < args.size()) {
            // explicit argument
            i++;
            args_expected_types.push_back(d);
            new_arg      = mk_metavar(d);
            args_mvars.push_back(new_arg);
            size_at_args.push_back(new_args.size());
        } else {
            break;
        }
        new_args.push_back(new_arg);
        /* See comment above at visit_default_app_core */
        type_before_whnf = instantiate(binding_body(type), new_arg);
        type             = whnf(type_before_whnf);
    }
    type = type_before_whnf;
    if (i != args.size()) {
        /* failed to consume all explicit arguments, use default elaboration for applications */
        C.restore(*this);
        return none_expr();
    }
    if (!is_def_eq(expected_type, type)) {
        /* failed to unify expected_type and computed type, use default elaboration for applications */
        C.restore(*this);
        return none_expr();
    }
    lean_assert(args_expected_types.size() == args.size());
    lean_assert(args_expected_types.size() == args_mvars.size());
    lean_assert(args_expected_types.size() == size_at_args.size());
    /* Second pass: visit explicit arguments using the information
       we gained about their expected types */
    for (unsigned i = 0; i < args.size(); i++) {
        expr ref_arg      = args[i];
        expr new_arg      = visit(args[i], some_expr(args_expected_types[i]));
        expr new_arg_type = infer_type(new_arg);
        if (optional<expr> new_new_arg = ensure_has_type(new_arg, new_arg_type, args_expected_types[i], ref_arg)) {
            new_arg = *new_new_arg;
        } else {
            new_args.shrink(size_at_args[i]);
            new_args.push_back(new_arg);
            format msg = mk_app_type_mismatch_error(mk_app(fn, new_args.size(), new_args.data()),
                                                    new_arg, new_arg_type, args_expected_types[i]);
            throw elaborator_exception(ref, msg);
        }
        if (!is_def_eq(args_mvars[i], new_arg)) {
            throw elaborator_exception(ref_arg, "invalid application, type mismatch when assigning auxiliary metavar");
        } else {
            new_args[size_at_args[i]] = new_arg;
        }
    }
    /* Put new instances on the stack */
    for (expr const & new_inst : new_instances)
        m_instance_stack = cons(new_inst, m_instance_stack);
    return some_expr(mk_app(fn, new_args.size(), new_args.data()));
}

bool elaborator::is_with_expected_candidate(expr const & fn) {
    /* We only propagate type to arguments for constructors. */
    if (!is_constant(fn)) return false;
    return
        static_cast<bool>(inductive::is_intro_rule(m_env, const_name(fn))) ||
        elab_with_expected_type(m_env, const_name(fn));
}

expr elaborator::visit_default_app_core(expr const & _fn, arg_mask amask, buffer<expr> const & args,
                                        bool args_already_visited, optional<expr> const & expected_type, expr const & ref) {
    expr fn      = _fn;
    expr fn_type = infer_type(fn);
    unsigned i = 0;
    buffer<expr> new_args;

    /** Check if this application is a candidate for propagating the expected type to arguments */
    if (!args_already_visited && /* if the arguments have already been visited, then there is no point. */
        expected_type &&         /* the expected type must be known */
        amask == arg_mask::Default && /* we do not propagate information when @ and @@ are used */
        is_with_expected_candidate(fn)) {
        if (auto r = visit_app_with_expected(fn, args, *expected_type, ref)) {
            return *r;
        }
    }

    /* We manually track the type before whnf. We do that because after the loop
       we check whether the application type is definitionally equal to expected_type.
       Suppose, the result type is (tactic expr) and the expected type is (?M1 ?M2).
       The unification problem can be solved using first-order unification, but if we
       unfold (tactic expr), we get (tactic_state -> base_tactic_result ...) which cannot.

       The statement
         expr type = try_to_pi(fn_type);
       also does not work because (tactic expr) unfolds into a type. */
    expr type_before_whnf = fn_type;
    expr type             = whnf(fn_type);
    while (true) {
        if (is_pi(type)) {
            binder_info const & bi = binding_info(type);
            expr const & d = binding_domain(type);
            expr new_arg;
            if (amask == arg_mask::Default && bi.is_strict_implicit() && i == args.size())
                break;
            if ((amask == arg_mask::Default && !is_explicit(bi)) ||
                (amask == arg_mask::Simple && !bi.is_inst_implicit() && !is_first_order(d))) {
                // implicit argument
                if (bi.is_inst_implicit())
                    new_arg = mk_instance(d, ref);
                else
                    new_arg = mk_metavar(d);
                // implicit arguments are tagged as inaccessible in patterns
                if (m_in_pattern)
                    new_arg = copy_tag(ref, mk_inaccessible(new_arg));
            } else if (i < args.size()) {
                // explicit argument
                expr ref_arg = args[i];
                if (args_already_visited)
                    new_arg = args[i];
                else
                    new_arg = visit(args[i], some_expr(d));
                expr new_arg_type = infer_type(new_arg);
                if (optional<expr> new_new_arg = ensure_has_type(new_arg, new_arg_type, d, ref_arg)) {
                    new_arg = *new_new_arg;
                } else {
                    new_args.push_back(new_arg);
                    format msg = mk_app_type_mismatch_error(mk_app(fn, new_args.size(), new_args.data()),
                                                            new_arg, new_arg_type, d);
                    throw elaborator_exception(ref, msg);
                }
                i++;
            } else {
                break;
            }
            new_args.push_back(new_arg);
            /* See comment above at first type_before_whnf assignment */
            type_before_whnf = instantiate(binding_body(type), new_arg);
            type             = whnf(type_before_whnf);
        } else if (i < args.size()) {
            expr new_fn = mk_app(fn, new_args.size(), new_args.data());
            new_args.clear();
            fn = ensure_function(new_fn, ref);
            type_before_whnf = infer_type(fn);
            type = whnf(type_before_whnf);
        } else {
            lean_assert(i == args.size());
            break;
        }
    }

    type = type_before_whnf;

    expr r = mk_app(fn, new_args.size(), new_args.data());
    if (expected_type) {
        trace_elab_debug(tout() << "application\n  " << r << "\nhas type\n  " <<
                         type << "\nexpected\n  " << *expected_type << "\nfunction type:\n  " <<
                         fn_type << "\n";);
        if (auto new_r = ensure_has_type(r, instantiate_mvars(type), *expected_type, ref)) {
            return *new_r;
        } else {
            /* We do not generate the error here because we can produce a better one from
               the caller (i.e., place the set the expected_type) */
        }
    }
    return r;
}

expr elaborator::visit_default_app(expr const & fn, arg_mask amask, buffer<expr> const & args,
                                   optional<expr> const & expected_type, expr const & ref) {
    return visit_default_app_core(fn, amask, args, false, expected_type, ref);
}

expr elaborator::visit_overload_candidate(expr const & fn, buffer<expr> const & args,
                                          optional<expr> const & expected_type, expr const & ref) {
    return visit_default_app_core(fn, arg_mask::Default, args, true, expected_type, ref);
}

void elaborator::throw_no_overload_applicable(buffer<expr> const & fns, buffer<elaborator_exception> const & error_msgs, expr const & ref) {
    format r("none of the overloads are applicable");
    lean_assert(error_msgs.size() == fns.size());
    for (unsigned i = 0; i < fns.size(); i++) {
        if (i > 0) r += line();
        auto pp_fn = mk_pp_ctx();
        format f_fmt = (is_constant(fns[i])) ? format(const_name(fns[i])) : pp_fn(fns[i]);
        r += line() + format("error for") + space() + f_fmt;
        r += line() + error_msgs[i].pp();
    }
    throw elaborator_exception(ref, r);
}

expr elaborator::visit_overloaded_app(buffer<expr> const & fns, buffer<expr> const & args,
                                      optional<expr> const & expected_type, expr const & ref) {
    trace_elab_detail(tout() << "overloaded application at " << pos_string_for(ref);
                      auto pp_fn = mk_pp_ctx();
                      tout() << pp_overloads(pp_fn, fns) << "\n";);
    list<expr> saved_instance_stack = m_instance_stack;
    buffer<expr> new_args;
    for (expr const & arg : args) {
        new_args.push_back(copy_tag(arg, visit(arg, none_expr())));
    }

    snapshot S(*this);

    buffer<pair<expr, snapshot>> candidates;
    buffer<elaborator_exception> error_msgs;
    for (expr const & fn : fns) {
        try {
            // Restore state
            S.restore(*this);
            bool has_args = !args.empty();
            expr new_fn   = visit_function(fn, has_args, ref);
            expr c        = visit_overload_candidate(new_fn, new_args, expected_type, ref);
            try_to_synthesize_type_class_instances(saved_instance_stack);

            if (expected_type) {
                expr c_type = infer_type(c);
                if (ensure_has_type(c, c_type, *expected_type, ref)) {
                    candidates.emplace_back(c, snapshot(*this));
                } else {
                    auto pp_fn = mk_pp_ctx();
                    throw elaborator_exception(ref, format("invalid overload, expression") + pp_indent(pp_fn, c) +
                                               line() + format("has type") + pp_indent(pp_fn, c_type) +
                                               line() + format("but is expected to have type") +
                                               pp_indent(pp_fn, *expected_type));
                }
            } else {
                candidates.emplace_back(c, snapshot(*this));
            }
        } catch (elaborator_exception & ex) {
            error_msgs.push_back(ex);
        } catch (exception & ex) {
            error_msgs.push_back(elaborator_exception(ref, format(ex.what())));
        }
    }
    lean_assert(candidates.size() + error_msgs.size() == fns.size());

    if (candidates.empty()) {
        S.restore(*this);

        throw_no_overload_applicable(fns, error_msgs, ref);
    } else if (candidates.size() > 1) {
        S.restore(*this);

        options new_opts = m_opts.update_if_undef(get_pp_full_names_name(), true);
        flet<options> set_opts(m_opts, new_opts);
        auto pp_fn = mk_pp_ctx();
        format r("ambiguous overload, possible interpretations");
        for (auto const & c : candidates) {
            r += pp_indent(pp_fn, c.first);
        }
        throw elaborator_exception(ref, r);
    } else {
        // Restore successful state
        candidates[0].second.restore(*this);
        return candidates[0].first;
    }
}

expr elaborator::visit_no_confusion(expr const & fn, buffer<expr> const & args, optional<expr> const & expected_type, expr const & ref) {
    name fn_name = const_name(fn);
    if (!expected_type) {
        throw elaborator_exception(ref, format("invalid '") + format(fn_name) + format ("' application, ") +
                                   format("elaborator has special support for no_confusion ") +
                                   format("but the expected type must be known"));
    }
    if (args.empty()) {
        throw elaborator_exception(ref,
                                   format("invalid occurrence of function '") + format(fn_name) +
                                   format ("', it must be applied to at least one argument (possible solution: use '@')"));
    }
    /* I.no_confusion functions have a type of the form

       Pi (params) (indices) (C : Type) (lhs rhs : I params indices) (H : lhs = rhs), I.no_confusion_type params indices C lhs rhs

       The type (I.no_confusion_type params indices C lhs rhs) is C if lhs and rhs are distinct constructors,
       and (Pi Hs, C) if they are the same constructor where Hs is a sequence of equalities.

       (C : Type) is the expected type.

       To make the elaborator more effective, we first elaborate the first explicit argument (i.e., args[0]) and obtain Heq,
       and create the fake pre-term

       (I.no_confusion _ ... _ (as-is expected_type) _ _ (as-is Heq) args[1] ... args[n-1])

       Then, we elaborate this new fake pre-term.
    */
    expr Heq      = checkpoint_visit(args[0], none_expr());
    name I_name   = fn_name.get_prefix();
    unsigned nparams  = *inductive::get_num_params(m_env, I_name);
    unsigned nindices = *inductive::get_num_indices(m_env, I_name);
    buffer<expr> new_args;
    for (unsigned i = 0; i < nparams + nindices; i++) {
        new_args.push_back(copy_tag(ref, mk_expr_placeholder()));
    }
    new_args.push_back(copy_tag(ref, mk_as_is(*expected_type)));
    new_args.push_back(copy_tag(ref, mk_expr_placeholder())); // lhs
    new_args.push_back(copy_tag(ref, mk_expr_placeholder())); // rhs
    new_args.push_back(copy_tag(args[0], mk_as_is(Heq)));
    for (unsigned i = 1; i < args.size(); i++)
        new_args.push_back(args[i]);
    return visit_default_app_core(fn, arg_mask::All, new_args, false, expected_type, ref);
}

expr elaborator::visit_app_core(expr fn, buffer<expr> const & args, optional<expr> const & expected_type,
                                expr const & ref) {
    arg_mask amask = arg_mask::Default;
    if (is_explicit(fn)) {
        fn   = get_explicit_arg(fn);
        amask = arg_mask::All;
    } else if (is_partial_explicit(fn)) {
        fn   = get_partial_explicit_arg(fn);
        amask = arg_mask::Simple;
    }

    bool has_args = !args.empty();

    if (is_choice(fn)) {
        buffer<expr> fns;
        if (amask != arg_mask::Default)
            throw elaborator_exception(ref, "invalid explicit annotation, symbol is overloaded "
                                       "(solution: use fully qualified names)");
        for (unsigned i = 0; i < get_num_choices(fn); i++) {
            expr const & fn_i = get_choice(fn, i);
            fns.push_back(fn_i);
        }
        validate_overloads(fns, ref);
        return visit_overloaded_app(fns, args, expected_type, ref);
    } else {
        expr new_fn = visit_function(fn, has_args, ref);
        /* Check if we should use a custom elaboration procedure for this application. */
        if (is_constant(new_fn) && amask == arg_mask::Default) {
            if (auto info = use_elim_elab(const_name(new_fn))) {
                if (args.size() >= info->m_nexplicit) {
                    return visit_elim_app(new_fn, *info, args, expected_type, ref);
                } else {
                    trace_elab(tout() << pos_string_for(ref) << " 'eliminator' elaboration is not used for '" << fn <<
                               "' because it is not fully applied, #" << info->m_nexplicit <<
                               " explicit arguments expected\n";);
                }
            } else if (is_no_confusion(m_env, const_name(new_fn))) {
                return visit_no_confusion(new_fn, args, expected_type, ref);
            }
        }
        return visit_default_app(new_fn, amask, args, expected_type, ref);
    }
}

expr elaborator::visit_local(expr const & e, optional<expr> const & expected_type) {
    return visit_app_core(e, buffer<expr>(), expected_type, e);
}

expr elaborator::visit_constant(expr const & e, optional<expr> const & expected_type) {
    return visit_app_core(e, buffer<expr>(), expected_type, e);
}

expr elaborator::visit_app(expr const & e, optional<expr> const & expected_type) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_equations(fn))
        return visit_convoy(e, expected_type);
    else
        return visit_app_core(fn, args, expected_type, e);
}

expr elaborator::visit_by(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_by(e));
    expr tac;
    {
        checkpoint C(*this);
        tac = visit(get_by_arg(e), some_expr(mk_tactic_unit()));
        process_checkpoint(C);
        tac = instantiate_mvars(tac);
    }
    expr mvar      = copy_tag(e, mk_metavar(expected_type));
    lean_assert(mvar == head(m_mvar_stack));
    // Remove mvar from m_mvar_stack, we keep mvars associated with tactics in a separate stack
    m_mvar_stack = tail(m_mvar_stack);
    m_tactic_stack = cons(mk_pair(mvar, tac), m_tactic_stack);
    trace_elab(tout() << "tactic for ?m_" << get_metavar_decl_ref_suffix(mvar) << " at " <<
               pos_string_for(mvar) << "\n" << tac << "\n";);
    return mvar;
}

expr elaborator::visit_anonymous_constructor(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_anonymous_constructor(e));
    buffer<expr> args;
    expr const & c = get_app_args(get_anonymous_constructor_arg(e), args);
    if (!expected_type)
        throw elaborator_exception(e, "invalid constructor ⟨...⟩, expected type must be known");
    expr I = get_app_fn(m_ctx.relaxed_whnf(instantiate_mvars(*expected_type)));
    if (!is_constant(I))
        throw elaborator_exception(e, format("invalid constructor ⟨...⟩, expected type is not an inductive type") +
                                   pp_indent(*expected_type));
    name I_name = const_name(I);
    if (is_private(m_env, I_name))
        throw elaborator_exception(e, "invalid constructor ⟨...⟩, type is a private inductive datatype");
    if (!inductive::is_inductive_decl(m_env, I_name))
        throw elaborator_exception(e, sstream() << "invalid constructor ⟨...⟩, '" << I_name << "' is not an inductive type");
    buffer<name> c_names;
    get_intro_rule_names(m_env, I_name, c_names);
    if (c_names.size() != 1)
        throw elaborator_exception(e, sstream() << "invalid constructor ⟨...⟩, '" << I_name << "' must have only one constructor");
    expr type = m_env.get(c_names[0]).get_type();
    unsigned num_explicit = 0;
    while (is_pi(type)) {
        if (is_explicit(binding_info(type)))
            num_explicit++;
        type = binding_body(type);
    }
    if (num_explicit > 1 && args.size() > num_explicit) {
        unsigned num_extra = args.size() - num_explicit;
        expr rest = copy_tag(e, mk_app(c, num_extra + 1, args.data() + num_explicit - 1));
        rest = copy_tag(e, mk_anonymous_constructor(rest));
        args.shrink(num_explicit);
        args.back() = rest;
    }
    expr new_e = copy_tag(e, mk_app(mk_constant(c_names[0]), args));
    return visit(new_e, expected_type);
}

static expr get_equations_fn_type(expr const & eqns) {
    buffer<expr> eqs;
    to_equations(eqns, eqs);
    lean_assert(!eqs.empty());
    lean_assert(is_lambda(eqs[0]));
    return binding_domain(eqs[0]);
}

static expr instantiate_rev(expr const & e, type_context::tmp_locals const & locals) {
    return instantiate_rev(e, locals.as_buffer().size(), locals.as_buffer().data());
}

static expr update_equations_fn_type(expr const & eqns, expr const & new_fn_type) {
    expr fn_type = mk_as_is(new_fn_type);
    buffer<expr> eqs;
    to_equations(eqns, eqs);
    for (expr & eq : eqs) {
        lean_assert(is_lambda(eq));
        eq = update_binding(eq, fn_type, binding_body(eq));
    }
    return update_equations(eqns, eqs);
}

expr elaborator::visit_convoy(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_app(e));
    lean_assert(is_equations(get_app_fn(e)));
    expr const & ref = e;
    buffer<expr> args, new_args;
    expr const & eqns = get_app_args(e, args);
    lean_assert(equations_num_fns(eqns) == 1);
    lean_assert(equations_size(eqns) > 0);
    expr fn_type = get_equations_fn_type(eqns);
    expr new_fn_type;
    if (is_placeholder(fn_type)) {
        /* User did not provide the type for the match,
           we try to infer one using expected_type and the type of the arguments */
        if (!expected_type)
            throw elaborator_exception(ref, "invalid match/convoy expression, expected type is not known");
        checkpoint C(*this);
        for (unsigned i = 0; i < args.size(); i++)
            new_args.push_back(visit(args[i], none_expr()));
        process_checkpoint(C);
        new_fn_type = *expected_type;
        unsigned i = args.size();
        while (i > 0) {
            --i;
            expr new_arg      = instantiate_mvars(new_args[i]);
            expr new_arg_type = instantiate_mvars(infer_type(new_arg));
            new_fn_type       = ::lean::mk_pi("_a", new_arg_type, kabstract(m_ctx, new_fn_type, new_arg));
        }
    } else {
        // User provided some typing information for the match
        type_context::tmp_locals locals(m_ctx);
        checkpoint C(*this);
        expr it = fn_type;
        for (unsigned i = 0; i < args.size(); i++) {
            if (!is_pi(it))
                throw elaborator_exception(it, "type expected in match-expression");
            expr d        = instantiate_rev(binding_domain(it), locals);
            expr new_d    = visit(d, none_expr());
            new_d         = ensure_type(new_d, binding_domain(it));
            expr expected = replace_locals(new_d, locals.as_buffer(), new_args);
            expr new_arg  = visit(args[i], some_expr(expected));
            new_arg       = enforce_type(new_arg, expected, "type mismatch in match expression", args[i]);
            locals.push_local(binding_name(it), new_d, binding_info(it));
            it            = binding_body(it);
            new_args.push_back(new_arg);
        }
        if (is_placeholder(it)) {
            process_checkpoint(C);
            if (!expected_type)
                throw elaborator_exception(ref, "invalid match/convoy expression, expected type is not known");
            new_fn_type = *expected_type;
            unsigned i = args.size();
            while (i > 0) {
                --i;
                new_args[i]  = instantiate_mvars(new_args[i]);
                new_fn_type  = instantiate(kabstract(m_ctx, new_fn_type, new_args[i]), locals.as_buffer()[i]);
            }
            new_fn_type = instantiate_mvars(locals.mk_pi(new_fn_type));
        } else {
            expr b      = instantiate_rev(it, locals);
            expr new_b  = visit(b, none_expr());
            process_checkpoint(C);
            new_fn_type = instantiate_mvars(locals.mk_pi(instantiate_mvars(new_b)));
        }
    }
    if (has_expr_metavar(new_fn_type)) {
        throw elaborator_exception(ref, "invalid match/convoy expression, type contains meta-variables");
    }
    trace_elab(tout() << "match/convoy function type: " << new_fn_type << "\n";);
    expr new_eqns = visit_equations(update_equations_fn_type(eqns, new_fn_type));
    expr fn       = get_equations_result(new_eqns, 0);
    return mk_app(fn, new_args);
}

/** \brief Given two binding expressions \c source and \c target
    s.t. they have at least \c num binders, replace the first \c num binders of \c target with \c source.
    The binder types are wrapped with \c mk_as_is to make sure the elaborator will not process
    them again. */
static expr copy_domain(unsigned num, expr const & source, expr const & target) {
    if (num == 0) {
        return target;
    } else {
        lean_assert(is_binding(source) && is_binding(target));
        return update_binding(source, mk_as_is(binding_domain(source)),
                              copy_domain(num-1, binding_body(source), binding_body(target)));
    }
}

static void check_equations_arity(buffer<expr> const & eqns) {
    buffer<optional<unsigned>> fidx2arity;
    for (expr eqn : eqns) {
        unsigned nbinders = 0;
        expr curr = eqn;
        while (is_lambda(eqn)) {
            nbinders++;
            eqn = binding_body(eqn);
        }
        if (is_equation(eqn)) {
            expr const & lhs = equation_lhs(eqn);
            expr const & fn  = get_app_fn(lhs);
            unsigned arity   = get_app_num_args(lhs);
            if (!is_var(fn) || var_idx(fn) >= nbinders)
                throw elaborator_exception(eqn, "ill-formed match/equations expression");
            unsigned fidx    = nbinders - var_idx(fn) - 1;
            if (fidx >= fidx2arity.size())
                fidx2arity.resize(fidx+1, optional<unsigned>());
            if (auto r = fidx2arity[fidx]) {
                if (*r != arity) {
                    throw elaborator_exception(eqn, "invalid match/equations expression, "
                                               "each case must have the same number of patterns");
                }
            } else {
                fidx2arity[fidx] = arity;
            }
        } else if (is_no_equation(eqn)) {
            /* do nothing */
        } else {
            throw elaborator_exception(curr, "ill-formed match/equations expression");
        }
    }
}

expr elaborator::visit_equations(expr const & e) {
    expr const & ref = e;
    buffer<expr> eqs;
    buffer<expr> new_eqs;
    optional<expr> new_R;
    optional<expr> new_Rwf;
    checkpoint C(*this);
    equations_header const & header = get_equations_header(e);
    unsigned num_fns = header.m_num_fns;
    to_equations(e, eqs);
    lean_assert(!eqs.empty());

    if (is_wf_equations(e)) {
        new_R   = visit(equations_wf_rel(e), none_expr());
        new_Rwf = visit(equations_wf_proof(e), none_expr());
        expr wf = mk_app(m_ctx, get_well_founded_name(), *new_R);
        new_Rwf = enforce_type(*new_Rwf, wf, "invalid well-founded relation proof", ref);
    }

    optional<expr> first_eq;
    for (expr const & eq : eqs) {
        expr new_eq;
        buffer<expr> fns_locals;
        fun_to_telescope(eq, fns_locals, optional<binder_info>());
        list<expr> locals = to_list(fns_locals.begin() + num_fns, fns_locals.end());
        if (first_eq) {
            // Replace first num_fns domains of eq with the ones in first_eq.
            // This is a trick/hack to ensure the fns in each equation have
            // the same elaborated type.
            new_eq   = copy_tag(eq, visit(copy_domain(num_fns, *first_eq, eq), none_expr()));
        } else {
            new_eq   = copy_tag(eq, visit(eq, none_expr()));
            first_eq = new_eq;
        }
        new_eqs.push_back(new_eq);
    }
    check_equations_arity(new_eqs);
    process_checkpoint(C);
    expr new_e;
    if (new_R) {
        new_e = copy_tag(e, mk_equations(header, new_eqs.size(), new_eqs.data(), *new_R, *new_Rwf));
    } else {
        new_e = copy_tag(e, mk_equations(header, new_eqs.size(), new_eqs.data()));
    }
    new_e = instantiate_mvars(new_e);
    ensure_no_unassigned_metavars(new_e);
    metavar_context mctx = m_ctx.mctx();
    expr r = compile_equations(m_env, m_opts, mctx, m_ctx.lctx(), new_e);
    m_ctx.set_env(m_env);
    m_ctx.set_mctx(mctx);
    return r;
}

void elaborator::check_pattern_inaccessible_annotations(expr const & p) {
    if (is_app(p)) {
        buffer<expr> args;
        expr const & c = get_app_args(p, args);
        if (is_constant(c)) {
            if (optional<name> I_name = inductive::is_intro_rule(m_env, const_name(c))) {
                /* Make sure the inductive datatype parameters are marked as inaccessible */
                unsigned nparams = *inductive::get_num_params(m_env, *I_name);
                for (unsigned i = 0; i < nparams && i < args.size(); i++) {
                    if (!is_inaccessible(args[i])) {
                        throw elaborator_exception(c, "invalid pattern, in a constructor application, "
                                                   "the parameters of the inductive datatype must be marked as inaccessible");
                    }
                }
            }
            // TODO(Leo): we should add a similar check for derived constructors.
            // What about constants marked as pattern? Example: @add
            // Option: check again at elim_match. The error message will not be nice,
            // but it is better than nothing.
        }
        for (expr const & a : args) {
            check_pattern_inaccessible_annotations(a);
        }
    }
}

void elaborator::check_inaccessible_annotations(expr const & lhs) {
    buffer<expr> patterns;
    get_app_args(lhs, patterns);
    for (expr const & p : patterns) {
        check_pattern_inaccessible_annotations(p);
    }
}

expr elaborator::visit_equation(expr const & eq) {
    expr const & lhs = equation_lhs(eq);
    expr const & rhs = equation_rhs(eq);
    expr lhs_fn = get_app_fn(lhs);
    if (is_explicit_or_partial_explicit(lhs_fn))
        lhs_fn = get_explicit_or_partial_explicit_arg(lhs_fn);
    if (!is_local(lhs_fn))
        throw exception("ill-formed equation");
    expr new_lhs;
    {
        list<expr> saved_instance_stack = m_instance_stack;
        flet<bool> set(m_in_pattern, true);
        new_lhs = visit(lhs, none_expr());
        check_inaccessible_annotations(new_lhs);
        try_to_synthesize_type_class_instances(saved_instance_stack);
    }
    expr new_lhs_type = instantiate_mvars(infer_type(new_lhs));
    expr new_rhs      = visit(rhs, some_expr(new_lhs_type));
    new_rhs = enforce_type(new_rhs, new_lhs_type, "equation type mismatch", eq);
    return copy_tag(eq, mk_equation(new_lhs, new_rhs));
}

expr elaborator::visit_inaccessible(expr const & e, optional<expr> const & expected_type) {
    if (!m_in_pattern)
        throw elaborator_exception(e, "invalid occurrence of 'inaccessible' annotation, "
                                   "it must only occur in patterns");
    expr m = copy_tag(e, mk_metavar(expected_type));
    expr a = get_annotation_arg(e);
    expr new_a;
    {
        flet<bool> set(m_in_pattern, false);
        new_a = visit(a, expected_type);
    }
    m_inaccessible_stack = cons(mk_pair(m, new_a), m_inaccessible_stack);
    return copy_tag(e, mk_inaccessible(m));
}

expr elaborator::visit_macro(expr const & e, optional<expr> const & expected_type, bool is_app_fn) {
    if (is_as_is(e)) {
        return get_as_is_arg(e);
    } else if (is_anonymous_constructor(e)) {
        if (is_app_fn)
            throw elaborator_exception(e, "invalid constructor ⟨...⟩, function expected");
        return visit_anonymous_constructor(e, expected_type);
    } else if (is_prenum(e)) {
        return visit_prenum(e, expected_type);
    } else if (is_typed_expr(e)) {
        return visit_typed_expr(e);
    } else if (is_choice(e) || is_explicit(e) || is_partial_explicit(e)) {
        return visit_app_core(e, buffer<expr>(), expected_type, e);
    } else if (is_by(e)) {
        return visit_by(e, expected_type);
    } else if (is_equations(e)) {
        lean_assert(!is_app_fn); // visit_convoy is used in this case
        return visit_equations(e);
    } else if (is_equation(e)) {
        lean_assert(!is_app_fn);
        return visit_equation(e);
    } else if (is_inaccessible(e)) {
        if (is_app_fn)
            throw elaborator_exception(e, "invalid inaccessible term, function expected");
        return visit_inaccessible(e, expected_type);
    } else if (is_no_info(e)) {
        // TODO(Leo): flet<bool> let(m_no_info, true);
        return visit(get_annotation_arg(e), expected_type);
    } else if (is_notation_info(e)) {
        // flet<bool> let(m_no_info, true);
        expr r = visit(get_annotation_arg(e), expected_type);
        // save_type_data(e, r);
        return r;
    } else if (is_as_atomic(e)) {
        /* ignore annotation */
        expr new_e = visit(get_as_atomic_arg(e), none_expr());
        if (is_app_fn)
            return new_e;
        /* If the as_atomic macro is not the the function in a function application, then we need to consume
           implicit arguments. */
        return visit_default_app_core(new_e, arg_mask::Default, buffer<expr>(), true, expected_type, e);
    } else if (is_annotation(e)) {
        expr r = visit(get_annotation_arg(e), expected_type);
        return update_macro(e, 1, &r);
    } else {
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(visit(macro_arg(e, i), none_expr()));
        return update_macro(e, args.size(), args.data());
    }
}

/* If the instance fingerprint has been set, then make sure `type` is not a local instance.
   Then, add a new local declaration to locals. */
expr elaborator::push_local(type_context::tmp_locals & locals,
                            name const & n, expr const & type, binder_info const & binfo, expr const & /* ref */) {
#if 0 // TODO(Leo): the following check is too restrictive
    if (m_ctx.lctx().get_instance_fingerprint() &&
        m_ctx.is_class(type)) {
        throw elaborator_exception(ref, "invalid occurrence of local instance, it must be a declaration parameter");
    }
#endif
    return locals.push_local(n, type, binfo);
}

/* See method above */
expr elaborator::push_let(type_context::tmp_locals & locals,
                          name const & n, expr const & type, expr const & value, expr const & /* ref */) {
#if 0 // TODO(Leo): the following check is too restrictive
    if (m_ctx.lctx().get_instance_fingerprint() &&
        m_ctx.is_class(type)) {
        throw elaborator_exception(ref, "invalid occurrence of local instance, it must be a declaration parameter");
    }
#endif
    return locals.push_let(n, type, value);
}

expr elaborator::visit_lambda(expr const & e, optional<expr> const & expected_type) {
    type_context::tmp_locals locals(m_ctx);
    checkpoint C(*this);
    expr it  = e;
    expr ex;
    bool has_expected;
    if (expected_type) {
        ex = instantiate_mvars(*expected_type);
        has_expected = true;
    } else {
        has_expected = false;
    }
    while (is_lambda(it)) {
        if (has_expected) {
            ex = try_to_pi(ex);
            if (!is_pi(ex))
                has_expected = false;
        }
        expr d     = instantiate_rev(binding_domain(it), locals);
        expr new_d = visit(d, none_expr());
        if (has_expected) {
            expr ex_d = binding_domain(ex);
            checkpoint C2(*this);
            if (is_def_eq(new_d, ex_d)) {
                C2.commit();
            }
        }
        new_d  = ensure_type(new_d, binding_domain(it));
        expr ref = binding_domain(it);
        expr l   = push_local(locals, binding_name(it), new_d, binding_info(it), ref);
        it = binding_body(it);
        if (has_expected) {
            lean_assert(is_pi(ex));
            ex = instantiate(binding_body(ex), l);
        }
    }
    expr b = instantiate_rev(it, locals);
    expr new_b;
    if (has_expected) {
        new_b = visit(b, some_expr(ex));
    } else {
        new_b = visit(b, none_expr());
    }
    process_checkpoint(C);
    expr r = locals.mk_lambda(new_b);
    return r;
}

expr elaborator::visit_pi(expr const & e) {
    type_context::tmp_locals locals(m_ctx);
    checkpoint C(*this);
    expr it  = e;
    while (is_pi(it)) {
        expr d     = instantiate_rev(binding_domain(it), locals);
        expr new_d = visit(d, none_expr());
        new_d      = ensure_type(new_d, binding_domain(it));
        expr ref   = binding_domain(it);
        push_local(locals, binding_name(it), new_d, binding_info(it), ref);
        it = binding_body(it);
    }
    expr b     = instantiate_rev(it, locals);
    expr new_b = visit(b, none_expr());
    new_b      = ensure_type(new_b, it);
    process_checkpoint(C);
    expr r = locals.mk_pi(new_b);
    return r;
}

expr elaborator::visit_let(expr const & e, optional<expr> const & expected_type) {
    expr ref = e;
    checkpoint C(*this);
    expr new_type  = visit(let_type(e), none_expr());
    expr new_value = visit(let_value(e), some_expr(new_type));
    new_value      = enforce_type(new_value, new_type, "invalid let-expression", let_value(e));
    process_checkpoint(C);
    new_type       = instantiate_mvars(new_type);
    new_value      = instantiate_mvars(new_value);
    type_context::tmp_locals locals(m_ctx);
    push_let(locals, let_name(e), new_type, new_value, ref);
    expr body      = instantiate_rev(let_body(e), locals);
    expr new_body  = visit(body, expected_type);
    expr new_e     = locals.mk_lambda(new_body);
    return new_e;
}

expr elaborator::visit_placeholder(expr const & e, optional<expr> const & expected_type) {
    return copy_tag(e, mk_metavar(expected_type));
}

static bool is_have_expr(expr const & e) {
    return is_app(e) && is_have_annotation(app_fn(e)) && is_lambda(get_annotation_arg(app_fn(e)));
}

expr elaborator::checkpoint_visit(expr const & e, optional<expr> const & expected_type) {
    checkpoint C(*this);
    expr r = visit(e, expected_type);
    process_checkpoint(C);
    return r;
}

expr elaborator::visit_have_expr(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_have_expr(e));
    expr lambda     = get_annotation_arg(app_fn(e));
    expr type       = binding_domain(lambda);
    expr proof      = app_arg(e);
    expr new_type   = checkpoint_visit(type, none_expr());
    new_type        = ensure_type(new_type, type);
    expr new_proof  = checkpoint_visit(proof, some_expr(new_type));
    new_proof       = enforce_type(new_proof, new_type, "invalid have-expression", proof);
    type_context::tmp_locals locals(m_ctx);
    expr ref        = binding_domain(lambda);
    push_local(locals, binding_name(lambda), new_type, binding_info(lambda), ref);
    expr body       = instantiate_rev(binding_body(lambda), locals);
    expr new_body   = visit(body, expected_type);
    expr new_lambda = locals.mk_lambda(new_body);
    return mk_app(mk_have_annotation(new_lambda), new_proof);
}

expr elaborator::visit_suffices_expr(expr const & e, optional<expr> const & expected_type) {
    lean_assert(is_suffices_annotation(e));
    expr body = get_annotation_arg(e);
    if (!is_app(body)) throw elaborator_exception(e, "ill-formed suffices expression");
    expr fn   = app_fn(body);
    expr rest = app_arg(body);
    if (!is_lambda(fn)) throw elaborator_exception(e, "ill-formed suffices expression");
    expr new_fn;
    expr type     = binding_domain(fn);
    expr new_type = checkpoint_visit(type, none_expr());
    {
        type_context::tmp_locals locals(m_ctx);
        expr ref        = binding_domain(fn);
        push_local(locals, binding_name(fn), new_type, binding_info(fn), ref);
        expr body       = instantiate_rev(binding_body(fn), locals);
        expr new_body   = checkpoint_visit(body, expected_type);
        new_fn          = locals.mk_lambda(new_body);
    }
    expr new_rest = visit(rest, some_expr(new_type));
    return mk_suffices_annotation(mk_app(new_fn, new_rest));
}

expr elaborator::visit(expr const & e, optional<expr> const & expected_type) {
    flet<unsigned> inc_depth(m_depth, m_depth+1);
    trace_elab_detail(tout() << "[" << m_depth << "] visiting\n" << e << "\n";);
    if (is_placeholder(e)) {
        return visit_placeholder(e, expected_type);
    } else if (is_have_expr(e)) {
        return visit_have_expr(e, expected_type);
    } else if (is_suffices_annotation(e)) {
        return visit_suffices_expr(e, expected_type);
    } else {
        switch (e.kind()) {
        case expr_kind::Var:        lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Meta:       return e;
        case expr_kind::Sort:       return visit_sort(e);
        case expr_kind::Local:      return visit_local(e, expected_type);
        case expr_kind::Constant:   return visit_constant(e, expected_type);
        case expr_kind::Macro:      return visit_macro(e, expected_type, false);
        case expr_kind::Lambda:     return visit_lambda(e, expected_type);
        case expr_kind::Pi:         return visit_pi(e);
        case expr_kind::App:        return visit_app(e, expected_type);
        case expr_kind::Let:        return visit_let(e, expected_type);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

expr elaborator::get_default_numeral_type() {
    // TODO(Leo): allow user to modify default?
    return mk_constant(get_nat_name());
}

void elaborator::ensure_numeral_types_assigned(checkpoint const & C) {
    list<expr> old_stack = C.m_saved_numeral_type_stack;
    while (!is_eqp(m_numeral_type_stack, old_stack)) {
        lean_assert(m_numeral_type_stack);
        expr A = instantiate_mvars(head(m_numeral_type_stack));
        if (is_metavar(A)) {
            if (!assign_mvar(A, get_default_numeral_type()))
                throw elaborator_exception(A, "invalid numeral, failed to force numeral to be a nat");
        }
        m_numeral_type_stack = tail(m_numeral_type_stack);
    }
}

void elaborator::synthesize_type_class_instances_core(list<expr> const & old_stack, bool force) {
    buffer<expr> to_keep;
    buffer<expr> to_process;
    while (!is_eqp(m_instance_stack, old_stack)) {
        lean_assert(m_instance_stack);
        lean_assert(is_metavar(head(m_instance_stack)));
        to_process.push_back(head(m_instance_stack));
        m_instance_stack   = tail(m_instance_stack);
    }
    unsigned i = to_process.size();
    while (i > 0) {
        --i;
        expr mvar          = to_process[i];
        expr ref           = mvar;
        metavar_decl mdecl = *m_ctx.mctx().get_metavar_decl(mvar);
        expr inst          = instantiate_mvars(mvar);
        if (!has_metavar(inst)) {
            trace_elab(tout() << "skipping type class resolution at " << pos_string_for(mvar)
                       << ", placeholder instantiated using type inference\n";);
            continue;
        }
        expr inst_type = instantiate_mvars(infer_type(inst));
        if (!has_expr_metavar(inst_type)) {
            // We must try to synthesize instance using the local context where it was declared
            if (!is_def_eq(inst, mk_instance_core(mdecl.get_context(), inst_type, ref)))
                throw elaborator_exception(mvar, "failed to assign type class instance to placeholder");
        } else {
            if (force) {
                lean_unreachable();
                auto pp_fn = mk_pp_ctx();
                throw elaborator_exception(mvar,
                                           format("type class instance cannot be synthesized, type has metavariables") +
                                           pp_indent(pp_fn, inst_type));
            } else {
                to_keep.push_back(mvar);
            }
        }
    }
    m_instance_stack = to_list(to_keep.begin(), to_keep.end(), m_instance_stack);
}

void elaborator::unassigned_uvars_to_params(level const & l) {
    if (!has_meta(l)) return;
    for_each(l, [&](level const & l) {
            if (!has_meta(l)) return false;
            if (is_meta(l) && !m_ctx.is_assigned(l)) {
                name r = mk_tagged_fresh_name(*g_level_prefix);
                m_ctx.assign(l, mk_param_univ(r));
            }
            return true;
        });
}

void elaborator::unassigned_uvars_to_params(expr const & e) {
    if (!has_univ_metavar(e)) return;
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_univ_metavar(e)) return false;
            if (is_constant(e)) {
                for (level const & l : const_levels(e))
                    unassigned_uvars_to_params(l);
            } else if (is_sort(e)) {
                unassigned_uvars_to_params(sort_level(e));
            }
            return true;
        });
}

static void throw_unsolved_tactic_state(tactic_state const & ts, format const & fmt, expr const & ref) {
    format msg = fmt + line() + format("state:") + line() + ts.pp();
    throw elaborator_exception(ref, msg);
}

static void throw_unsolved_tactic_state(tactic_state const & ts, char const * msg, expr const & ref) {
    throw_unsolved_tactic_state(ts, format(msg), ref);
}

tactic_state elaborator::mk_tactic_state_for(expr const & mvar) {
    metavar_context mctx = m_ctx.mctx();
    metavar_decl mdecl   = *mctx.get_metavar_decl(mvar);
    local_context lctx   = mdecl.get_context().instantiate_mvars(mctx);
    expr type            = mctx.instantiate_mvars(mdecl.get_type());
    m_ctx.set_mctx(mctx);
    return ::lean::mk_tactic_state_for(m_env, m_opts, mctx, lctx, type);
}

void elaborator::invoke_tactic(expr const & mvar, expr const & tactic) {
    expr const & ref = mvar;
    /* Build initial state */
    trace_elab(tout() << "executing tactic at " << pos_string_for(ref) << "\n";);
    tactic_state s       = mk_tactic_state_for(mvar);
    metavar_context mctx = m_ctx.mctx();
    trace_elab(tout() << "initial tactic state\n" << s.pp() << "\n";);

    /* Compile tactic into bytecode */
    name tactic_name("_tactic");
    expr tactic_type = mk_tactic_unit();
    environment new_env = m_env;
    bool use_conv_opt    = true;
    bool is_trusted      = false;
    auto cd = check(new_env, mk_definition(new_env, tactic_name, {}, tactic_type, tactic, use_conv_opt, is_trusted));
    new_env = new_env.add(cd);
    new_env = vm_compile(new_env, new_env.get(tactic_name));

    /* Invoke tactic */
    vm_state S(new_env);
    vm_obj r = S.invoke(tactic_name, to_obj(s));

    if (optional<tactic_state> new_s = is_tactic_success(r)) {
        trace_elab(tout() << "tactic at " << pos_string_for(ref) << " succeeded\n";);
        mctx     = new_s->mctx();
        expr val = mctx.instantiate_mvars(new_s->main());
        if (has_expr_metavar(val)) {
            throw_unsolved_tactic_state(*new_s, "tactic failed, result contains meta-variables", ref);
        }
        mctx.assign(mvar, val);
        m_env = new_s->env();
        m_ctx.set_env(m_env);
        m_ctx.set_mctx(mctx);
    } else if (optional<pair<format, tactic_state>> ex = is_tactic_exception(S, m_opts, r)) {
        throw_unsolved_tactic_state(ex->second, ex->first, ref);
    } else {
        lean_unreachable();
    }
}

// Auxiliary procedure for #translate
static expr translate_local_name(environment const & env, local_context const & lctx, name const & local_name,
                                 expr const & src) {
    if (auto decl = lctx.get_local_decl_from_user_name(local_name)) {
        return decl->mk_ref();
    }
    if (env.find(local_name)) {
        if (is_local(src))
            return mk_constant(local_name);
        else
            return src;
    }
    throw elaborator_exception(src, format("unknown identifier '") + format(local_name) + format("'"));
}

/** \brief Translated local constants (and undefined constants) occurring in \c e into
    local constants provided by \c ctx.
    Throw exception is \c ctx does not contain the local constant.
*/
static expr translate(environment const & env, local_context const & lctx, expr const & e) {
    auto fn = [&](expr const & e) {
        if (is_placeholder(e) || is_by(e) || is_as_is(e)) {
            return some_expr(e); // ignore placeholders, nested tactics and as_is terms
        } else if (is_constant(e)) {
            expr new_e = copy_tag(e, translate_local_name(env, lctx, const_name(e), e));
            return some_expr(new_e);
        } else if (is_local(e)) {
            expr new_e = copy_tag(e, translate_local_name(env, lctx, local_pp_name(e), e));
            return some_expr(new_e);
        } else {
            return none_expr();
        }
    };
    return replace(e, fn);
}

void elaborator::invoke_tactics(checkpoint const & C) {
    buffer<expr_pair> to_process;
    list<expr_pair> old_stack = C.m_saved_tactic_stack;
    while (!is_eqp(m_tactic_stack, old_stack)) {
        to_process.push_back(head(m_tactic_stack));
        m_tactic_stack = tail(m_tactic_stack);
    }
    if (to_process.empty()) return;

    elaborate_fn fn(nested_elaborate);
    scope_elaborate_fn scope(fn);

    unsigned i = to_process.size();
    while (i > 0) {
        --i;
        expr_pair const & p = to_process[i];
        lean_assert(is_metavar(p.first));
        invoke_tactic(p.first, p.second);
    }
}

void elaborator::ensure_no_unassigned_metavars(expr const & e) {
    if (!has_expr_metavar(e)) return;
    metavar_context mctx = m_ctx.mctx();
    for_each(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e)) return false;
            if (is_metavar_decl_ref(e) && !mctx.is_assigned(e)) {
                tactic_state s = mk_tactic_state_for(e);
                throw_unsolved_tactic_state(s, "don't know how to synthesize placeholder", e);
            }
            return true;
        });
}

void elaborator::check_inaccessible(checkpoint const & C) {
    buffer<expr_pair> to_process;
    list<expr_pair> old_stack = C.m_saved_inaccessible_stack;
    while (!is_eqp(m_inaccessible_stack, old_stack)) {
        to_process.push_back(head(m_inaccessible_stack));
        m_inaccessible_stack = tail(m_inaccessible_stack);
    }
    if (to_process.empty()) return;

    unsigned i = to_process.size();
    while (i > 0) {
        --i;
        expr_pair const & p = to_process[i];
        expr const & m = p.first;
        lean_assert(is_metavar(m));
        if (!m_ctx.is_assigned(m)) {
            throw elaborator_exception(m, "invalid use of inaccessible term, it is not fixed by other arguments");
        }
        expr v = instantiate_mvars(m);
        if (has_expr_metavar(v)) {
            throw elaborator_exception(m, format("invalid use of inaccessible term, it is not completely fixed by other arguments") +
                                       pp_indent(v));
        }
        if (!is_def_eq(v, p.second)) {
            auto pp_fn = mk_pp_ctx();
            throw elaborator_exception(m, format("invalid use of inaccessible term, the provided term is") +
                                       pp_indent(pp_fn, p.second) +
                                       line() + format("but is expected to be") +
                                       pp_indent(pp_fn, v));
        }
    }
}

void elaborator::process_checkpoint(checkpoint & C) {
    ensure_numeral_types_assigned(C);
    synthesize_type_class_instances(C);
    invoke_tactics(C);
    check_inaccessible(C);
    C.commit();
}

elaborator::base_snapshot::base_snapshot(elaborator const & e) {
    m_saved_mctx               = e.m_ctx.mctx();
    m_saved_instance_stack     = e.m_instance_stack;
    m_saved_numeral_type_stack = e.m_numeral_type_stack;
    m_saved_tactic_stack       = e.m_tactic_stack;
    m_saved_inaccessible_stack = e.m_inaccessible_stack;
}

void elaborator::base_snapshot::restore(elaborator & e) {
    e.m_ctx.set_mctx(m_saved_mctx);
    e.m_instance_stack     = m_saved_instance_stack;
    e.m_numeral_type_stack = m_saved_numeral_type_stack;
    e.m_tactic_stack       = m_saved_tactic_stack;
    e.m_inaccessible_stack = m_saved_inaccessible_stack;
}

elaborator::snapshot::snapshot(elaborator const & e):
    base_snapshot(e) {
    m_saved_mvar_stack = e.m_mvar_stack;
    m_saved_uvar_stack = e.m_uvar_stack;
}

void elaborator::snapshot::restore(elaborator & e) {
    base_snapshot::restore(e);
    e.m_mvar_stack = m_saved_mvar_stack;
    e.m_uvar_stack = m_saved_uvar_stack;
}

elaborator::checkpoint::checkpoint(elaborator & e):
    base_snapshot(e),
    m_elaborator(e),
    m_commit(false) {}

elaborator::checkpoint::~checkpoint() {
    if (!m_commit) {
        restore(m_elaborator);
    }
}

void elaborator::checkpoint::commit() {
    m_commit = true;
}

/**
    \brief Auxiliary class for creating nice names for universe
    parameters introduced by the elaborator.

    This class also transforms remaining universe metavariables
    into parameters */
struct sanitize_param_names_fn : public replace_visitor {
    type_context &  m_ctx;
    name            m_p{"l"};
    name_set        m_L; /* All parameter names in the input expression. */
    name_map<level> m_R; /* map from tagged g_level_prefix to "clean" name not in L. */
    name_map<level> m_U; /* map from universe metavariable name to "clean" name not in L. */
    unsigned        m_idx{1};
    bool            m_sanitized{false};
    buffer<name> &  m_new_param_names;

    sanitize_param_names_fn(type_context & ctx, buffer<name> & new_lp_names):
        m_ctx(ctx), m_new_param_names(new_lp_names) {}

    level mk_param() {
        while (true) {
            name new_n = m_p.append_after(m_idx);
            m_idx++;
            if (!m_L.contains(new_n)) {
                m_new_param_names.push_back(new_n);
                return mk_param_univ(new_n);
            }
        }
    }

    level sanitize(level const & l) {
        name p("l");
        return replace(l, [&](level const & l) -> optional<level> {
                if (is_param(l)) {
                    name const & n = param_id(l);
                    if (is_tagged_by(n, *g_level_prefix)) {
                        if (auto new_l = m_R.find(n)) {
                            return some_level(*new_l);
                        } else {
                            level r = mk_param();
                            m_R.insert(n, r);
                            return some_level(r);
                        }
                    }
                } else if (is_meta(l)) {
                    if (is_metavar_decl_ref(l) && m_ctx.is_assigned(l)) {
                        return some_level(sanitize(*m_ctx.get_assignment(l)));
                    } else {
                        name const & n = meta_id(l);
                        if (auto new_l = m_U.find(n)) {
                            return some_level(*new_l);
                        } else {
                            level r = mk_param();
                            m_U.insert(n, r);
                            return some_level(r);
                        }
                    }
                }
                return none_level();
            });
    }

    virtual expr visit_constant(expr const & e) override {
        return update_constant(e, map(const_levels(e), [&](level const & l) { return sanitize(l); }));
    }

    virtual expr visit_sort(expr const & e) override {
        return update_sort(e, sanitize(sort_level(e)));
    }

    void collect_params(expr const & e) {
        lean_assert(!m_sanitized);
        m_L = collect_univ_params(e, m_L);
    }

    void collect_local_context_params() {
        lean_assert(!m_sanitized);
        m_ctx.lctx().for_each([&](local_decl const & l) {
                collect_params(m_ctx.instantiate_mvars(l.get_type()));
                if (auto v = l.get_value())
                    collect_params(m_ctx.instantiate_mvars(*v));
            });
    }

    expr sanitize(expr const & e) {
        expr r = operator()(e);
        m_sanitized = true;
        return r;
    }
};

/** When the output of the elaborator may contain meta-variables, we convert the type_context level meta-variables
    into regular kernel meta-variables. */
static expr replace_with_simple_metavars(metavar_context mctx, name_map<expr> & cache, expr const & e) {
    if (!has_expr_metavar(e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!is_metavar(e)) return none_expr();
            if (auto r = cache.find(mlocal_name(e))) {
                return some_expr(*r);
            } else if (auto decl = mctx.get_metavar_decl(e)) {
                expr new_type = replace_with_simple_metavars(mctx, cache, mctx.instantiate_mvars(decl->get_type()));
                expr new_mvar = mk_metavar(mlocal_name(e), new_type);
                cache.insert(mlocal_name(e), new_mvar);
                return some_expr(new_mvar);
            } else if (is_metavar_decl_ref(e)) {
                throw exception("unexpected occurrence of internal elaboration metavariable");
            }
            return none_expr();
        });
}

expr elaborator::elaborate(expr const & e) {
    checkpoint C(*this);
    expr r = visit(e,  none_expr());
    trace_elab_detail(tout() << "result before final checkpoint\n" << r << "\n";);
    process_checkpoint(C);
    return r;
}

expr elaborator::elaborate_type(expr const & e) {
    expr Type  = copy_tag(e, mk_sort(mk_level_placeholder()));
    expr new_e = copy_tag(e, mk_typed_expr(Type, e));
    return elaborate(e);
}

expr_pair elaborator::elaborate_with_type(expr const & e, expr const & e_type) {
    expr const & ref = e;
    expr new_e, new_e_type;
    {
        checkpoint C(*this);
        expr Type  = visit(copy_tag(e_type, mk_sort(mk_level_placeholder())), none_expr());
        new_e_type = visit(e_type, some_expr(Type));
        new_e      = visit(e,      some_expr(new_e_type));
        process_checkpoint(C);
    }
    expr inferred_type = infer_type(new_e);
    if (auto r = ensure_has_type(new_e, inferred_type, new_e_type, ref)) {
        new_e = *r;
    } else {
        auto pp_fn = mk_pp_ctx();
        throw elaborator_exception(ref,
                                   format("type mismatch, expression") + pp_indent(pp_fn, new_e) +
                                   line() + format("has type") + pp_indent(pp_fn, inferred_type) +
                                   line() + format("but is expected to have type") + pp_indent(pp_fn, new_e_type));
    }
    return mk_pair(new_e, new_e_type);
}

void elaborator::finalize(buffer<expr> & es, buffer<name> & new_lp_names, bool check_unassigned, bool to_simple_metavar) {
    sanitize_param_names_fn S(m_ctx, new_lp_names);
    name_map<expr> to_simple_mvar_cache;
    for (expr & e : es) {
        e = instantiate_mvars(e);
        if (check_unassigned)
            ensure_no_unassigned_metavars(e);
        if (!check_unassigned && to_simple_metavar) {
            e = replace_with_simple_metavars(m_ctx.mctx(), to_simple_mvar_cache, e);
        }
        unassigned_uvars_to_params(e);
        e = instantiate_mvars(e);
        S.collect_params(e);
    }
    S.collect_local_context_params();
    for (expr & e : es) {
        e = S.sanitize(e);
    }
}

pair<expr, level_param_names> elaborator::finalize(expr const & e, bool check_unassigned, bool to_simple_metavar) {
    buffer<expr> es; es.push_back(e);
    buffer<name> new_lp_names;
    finalize(es, new_lp_names, check_unassigned, to_simple_metavar);
    return mk_pair(es[0], to_list(new_lp_names));
}

pair<expr, level_param_names>
elaborate(environment & env, options const & opts,
          metavar_context & mctx, local_context const & lctx, expr const & e,
          bool check_unassigned) {
    elaborator elab(env, opts, mctx, lctx);
    expr r = elab.elaborate(e);
    auto p = elab.finalize(r, check_unassigned, true);
    mctx = elab.mctx();
    env  = elab.env();
    return p;
}

expr nested_elaborate(environment & env, options const & opts, metavar_context & mctx, local_context const & lctx,
                      expr const & e, bool relaxed) {
    elaborator elab(env, opts, mctx, lctx);
    expr r = elab.elaborate(translate(env, lctx, e));
    if (!relaxed)
        elab.ensure_no_unassigned_metavars(e);
    mctx = elab.mctx();
    env  = elab.env();
    return r;
}

void initialize_elaborator() {
    g_elab_with_expected_type = new name("elab_with_expected_type");
    g_elab_as_eliminator      = new name("elab_as_eliminator");
    g_level_prefix = new name("_elab_u");
    register_trace_class("elaborator");
    register_trace_class("elaborator_detail");
    register_trace_class("elaborator_debug");
    register_system_attribute(basic_attribute(*g_elab_with_expected_type,
                                              "instructs elaborator that the arguments of the function application (f ...) "
                                              "should be elaborated using information about the expected type"));
    register_system_attribute(basic_attribute(*g_elab_as_eliminator,
                                              "instructs elaborator that the arguments of the function application (f ...) "
                                              "should be elaborated as f were an eliminator"));
}

void finalize_elaborator() {
    delete g_level_prefix;
    delete g_elab_with_expected_type;
    delete g_elab_as_eliminator;
}
}
