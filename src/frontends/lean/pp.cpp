/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include <limits>
#include <string>
#include <util/utf8.h>
#include "util/flet.h"
#include "util/fresh_name.h"
#include "kernel/replace_fn.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/annotation.h"
#include "library/aliases.h"
#include "library/scoped_ext.h"
#include "library/expr_pair.h"
#include "library/placeholder.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/quote.h"
#include "library/explicit.h"
#include "library/typed_expr.h"
#include "library/num.h"
#include "library/util.h"
#include "library/print.h"
#include "library/pp_options.h"
#include "library/delayed_abstraction.h"
#include "library/constants.h"
#include "library/replace_visitor.h"
#include "library/string.h"
#include "library/type_context.h"
#include "library/idx_metavar.h"
#include "library/equations_compiler/equations.h"
#include "library/tactic/tactic_state.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/rec_fn_macro.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/util.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/local_ref_info.h"
#include "frontends/lean/scanner.h"

namespace lean {
static format * g_ellipsis_n_fmt  = nullptr;
static format * g_ellipsis_fmt    = nullptr;
static format * g_placeholder_fmt = nullptr;
static format * g_lambda_n_fmt    = nullptr;
static format * g_lambda_fmt      = nullptr;
static format * g_forall_n_fmt    = nullptr;
static format * g_forall_fmt      = nullptr;
static format * g_pi_n_fmt        = nullptr;
static format * g_pi_fmt          = nullptr;
static format * g_arrow_n_fmt     = nullptr;
static format * g_arrow_fmt       = nullptr;
static format * g_let_fmt         = nullptr;
static format * g_in_fmt          = nullptr;
static format * g_assign_fmt      = nullptr;
static format * g_have_fmt        = nullptr;
static format * g_from_fmt        = nullptr;
static format * g_visible_fmt     = nullptr;
static format * g_show_fmt        = nullptr;
static format * g_explicit_fmt    = nullptr;
static format * g_partial_explicit_fmt    = nullptr;
static name   * g_tmp_prefix      = nullptr;

class nat_numeral_pp {
    expr m_num_type;
    name m_nat;
    expr m_nat_of_num;
    expr m_nat_zero;
    expr m_nat_succ;
public:
    nat_numeral_pp():
        m_num_type(mk_constant(get_Num_name())),
        m_nat(get_Nat_name()),
        m_nat_of_num(mk_constant(get_Nat_ofNum_name())),
        m_nat_zero(mk_constant(get_Nat_zero_name())),
        m_nat_succ(mk_constant(get_Nat_succ_name())) {
    }

    // Return an unsigned if \c e if of the form (succ^k zero), and k
    // fits in a machine unsigned integer.
    optional<unsigned> to_unsigned(expr const & e) const {
        unsigned r = 0;
        expr const * it = &e;
        while (true) {
            if (*it == m_nat_zero) {
                return optional<unsigned>(r);
            } else if (is_app(*it) && app_fn(*it) == m_nat_succ) {
                if (r == std::numeric_limits<unsigned>::max())
                    return optional<unsigned>(); // just in case, it does not really happen in practice
                r++;
                it = &app_arg(*it);
            } else if (is_constant(get_app_fn(*it), get_zero_name())) {
                return optional<unsigned>(r);
            } else {
                return optional<unsigned>();
            }
        }
    }
};

static nat_numeral_pp * g_nat_numeral_pp = nullptr;

static optional<unsigned> to_unsigned(expr const & e) {
    return g_nat_numeral_pp->to_unsigned(e);
}

void initialize_pp() {
    g_ellipsis_n_fmt  = new format(highlight(format("\u2026")));
    g_ellipsis_fmt    = new format(highlight(format("...")));
    g_placeholder_fmt = new format(highlight(format("_")));
    g_lambda_n_fmt    = new format(highlight_keyword(format("\u03BB")));
    g_lambda_fmt      = new format(highlight_keyword(format("fun")));
    g_forall_n_fmt    = new format(highlight_keyword(format("\u2200")));
    g_forall_fmt      = new format(highlight_keyword(format("forall")));
    g_pi_n_fmt        = new format(highlight_keyword(format("Π")));
    g_pi_fmt          = new format(highlight_keyword(format("Pi")));
    g_arrow_n_fmt     = new format(highlight_keyword(format("\u2192")));
    g_arrow_fmt       = new format(highlight_keyword(format("->")));
    g_let_fmt         = new format(highlight_keyword(format("let")));
    g_in_fmt          = new format(highlight_keyword(format("in")));
    g_assign_fmt      = new format(highlight_keyword(format(":=")));
    g_have_fmt        = new format(highlight_keyword(format("have")));
    g_from_fmt        = new format(highlight_keyword(format("from")));
    g_visible_fmt     = new format(highlight_keyword(format("[visible]")));
    g_show_fmt        = new format(highlight_keyword(format("show")));
    g_explicit_fmt    = new format(highlight_keyword(format("@")));
    g_partial_explicit_fmt    = new format(highlight_keyword(format("@@")));
    g_tmp_prefix      = new name(name::mk_internal_unique_name());
    g_nat_numeral_pp  = new nat_numeral_pp();
}

void finalize_pp() {
    delete g_nat_numeral_pp;
    delete g_ellipsis_n_fmt;
    delete g_ellipsis_fmt;
    delete g_placeholder_fmt;
    delete g_lambda_n_fmt;
    delete g_lambda_fmt;
    delete g_forall_n_fmt;
    delete g_forall_fmt;
    delete g_pi_n_fmt;
    delete g_pi_fmt;
    delete g_arrow_n_fmt;
    delete g_arrow_fmt;
    delete g_let_fmt;
    delete g_in_fmt;
    delete g_assign_fmt;
    delete g_have_fmt;
    delete g_from_fmt;
    delete g_visible_fmt;
    delete g_show_fmt;
    delete g_partial_explicit_fmt;
    delete g_explicit_fmt;
    delete g_tmp_prefix;
}

/** \brief We assume a metavariable name has a suggestion embedded in it WHEN its
    last component is a string. */
static bool has_embedded_suggestion(name const & m) {
    return m.is_string();
}

/** \see extract_suggestion */
static name extract_suggestion_core(name const & m) {
    if (m.is_string()) {
        if (m.is_atomic())
            return m;
        else
            return name(extract_suggestion_core(m.get_prefix()), m.get_string());
    } else {
        return name();
    }
}

/** \brief Extract "suggested name" embedded in a metavariable name

    \pre has_embedded_suggestion(m)
*/
static name extract_suggestion(name const & m) {
    lean_assert(has_embedded_suggestion(m));
    name r = extract_suggestion_core(m);
    lean_assert(!r.is_anonymous());
    return r;
}

name pretty_fn::mk_metavar_name(name const & m, optional<name> const & prefix) {
    if (auto it = m_purify_meta_table.find(m))
        return *it;
    if (has_embedded_suggestion(m)) {
        name suggested = extract_suggestion(m);
        name r         = suggested;
        unsigned i     = 1;
        while (m_purify_used_metas.contains(r)) {
            r = suggested.append_after(i);
            i++;
        }
        m_purify_used_metas.insert(r);
        m_purify_meta_table.insert(m, r);
        return r;
    } else {
        name new_m;
        if (prefix)
            new_m = prefix->append_after(m_next_meta_idx);
        else
            new_m = m_meta_prefix.append_after(m_next_meta_idx);
        m_next_meta_idx++;
        m_purify_meta_table.insert(m, new_m);
        return new_m;
    }
}

name pretty_fn::mk_local_name(name const & n, name const & suggested) {
    if (!m_purify_locals)
        return suggested;
    if (auto it = m_purify_local_table.find(n))
        return *it;
    unsigned i = 1;
    name r = suggested;
    while (m_purify_used_locals.contains(r)) {
        r = suggested.append_after(i);
        i++;
    }
    m_purify_used_locals.insert(r);
    m_purify_local_table.insert(n, r);
    return r;
}

level pretty_fn::purify(level const & l) {
    if (!m_universes || !m_purify_metavars || !has_meta(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l))
                return some_level(l);
            if (is_metavar_decl_ref(l))
                return some_level(mk_meta_univ(mk_metavar_name(meta_id(l), "l")));
            if (is_meta(l) && !is_idx_metauniv(l))
                return some_level(mk_meta_univ(mk_metavar_name(meta_id(l))));
            return none_level();
        });
}

expr pretty_fn::infer_type(expr const & e) {
    try {
        return m_ctx.infer(e);
    } catch (exception &) {
        expr dummy = mk_Prop();
        return dummy;
    }
}

/** \brief Make sure that all metavariables have reasonable names,
    and for all local constants l1 l2, local_pp_name(l1) != local_pp_name(l2).

    \remark pretty_fn will create new local constants when pretty printing,
    but it will make sure that the new constants will not produce collisions.
*/
expr pretty_fn::purify(expr const & e) {
    if (!has_expr_metavar(e) && !has_local(e) && (!m_universes || !has_univ_metavar(e)))
        return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_local(e) && (!m_universes || !has_univ_metavar(e))) {
                return some_expr(e);
            } else if (is_metavar_decl_ref(e) && m_purify_metavars) {
                return some_expr(mk_metavar(mk_metavar_name(mlocal_name(e), "m"), infer_type(e)));
            } else if (is_metavar(e) && !is_idx_metavar(e) && m_purify_metavars) {
                return some_expr(mk_metavar(mk_metavar_name(mlocal_name(e)), infer_type(e)));
            } else if (is_local(e)) {
                return some_expr(mk_local(mlocal_name(e), mk_local_name(mlocal_name(e), local_pp_name(e)),
                                          infer_type(e), local_info(e)));
            } else if (is_constant(e)) {
                return some_expr(update_constant(e, map(const_levels(e), [&](level const & l) { return purify(l); })));
            } else if (is_sort(e)) {
                return some_expr(update_sort(e, purify(sort_level(e))));
            } else {
                return none_expr();
            }
        });
}

void pretty_fn::set_options_core(options const & _o) {
    options o = _o;
    bool all          = get_pp_all(o);
    if (all) {
        o = o.update_if_undef(get_pp_implicit_name(), true);
        o = o.update_if_undef(get_pp_proofs_name(), true);
        o = o.update_if_undef(get_pp_coercions_name(), true);
        o = o.update_if_undef(get_pp_notation_name(), false);
        o = o.update_if_undef(get_pp_universes_name(), true);
        o = o.update_if_undef(get_pp_full_names_name(), true);
        o = o.update_if_undef(get_pp_beta_name(), false);
        o = o.update_if_undef(get_pp_numerals_name(), false);
        o = o.update_if_undef(get_pp_strings_name(), false);
        o = o.update_if_undef(get_pp_binder_types_name(), true);
    }
    m_options           = o;
    m_indent            = get_pp_indent(o);
    m_max_depth         = get_pp_max_depth(o);
    m_max_steps         = get_pp_max_steps(o);
    m_implict           = get_pp_implicit(o);
    m_proofs            = get_pp_proofs(o);
    m_unicode           = get_pp_unicode(o);
    m_coercion          = get_pp_coercions(o);
    m_notation          = get_pp_notation(o);
    m_universes         = get_pp_universes(o);
    m_full_names        = get_pp_full_names(o);
    m_private_names     = get_pp_private_names(o);
    m_purify_metavars   = get_pp_purify_metavars(o);
    m_purify_locals     = get_pp_purify_locals(o);
    m_locals_full_names = get_pp_locals_full_names(o);
    m_beta              = get_pp_beta(o);
    m_numerals          = get_pp_numerals(o);
    m_strings           = get_pp_strings(o);
    m_preterm           = get_pp_preterm(o);
    m_binder_types      = get_pp_binder_types(o);
    m_hide_comp_irrel   = get_pp_hide_comp_irrel(o);
    m_delayed_abstraction  = get_pp_delayed_abstraction(o);
    m_hide_full_terms   = get_formatter_hide_full_terms(o);
    m_num_nat_coe       = m_numerals;
}

void pretty_fn::set_options(options const & o) {
    if (is_eqp(o, m_options))
        return;
    set_options_core(o);
}

format pretty_fn::pp_child(level const & l) {
    if (is_explicit(l) || is_param(l) || is_meta(l) || is_global(l)) {
        return pp_level(l);
    } else {
        return paren(pp_level(l));
    }
}

format pretty_fn::pp_max(level l) {
    lean_assert(is_max(l) || is_imax(l));
    format r  = format(is_max(l) ? "max" : "imax");
    level lhs = is_max(l) ? max_lhs(l) : imax_lhs(l);
    level rhs = is_max(l) ? max_rhs(l) : imax_rhs(l);
    r += nest(m_indent, compose(line(), pp_child(lhs)));
    while (kind(rhs) == kind(l)) {
        l = rhs;
        lhs = is_max(l) ? max_lhs(l) : imax_lhs(l);
        rhs = is_max(l) ? max_rhs(l) : imax_rhs(l);
        r += nest(m_indent, compose(line(), pp_child(lhs)));
    }
    r += nest(m_indent, compose(line(), pp_child(rhs)));
    return group(r);
}

format pretty_fn::pp_meta(level const & l) {
    if (m_universes) {
        if (is_idx_metauniv(l)) {
            return format((sstream() << "?u_" << to_meta_idx(l)).str());
        } else if (is_metavar_decl_ref(l)) {
            return format((sstream() << "?l_" << get_metavar_decl_ref_suffix(l)).str());
        } else {
            return compose(format("?"), format(meta_id(l)));
        }
    } else {
        return format("?");
    }
}

format pretty_fn::pp_level(level const & l) {
    if (is_explicit(l)) {
        lean_assert(get_depth(l) > 0);
        return format(get_depth(l) - 1);
    } else {
        switch (kind(l)) {
        case level_kind::Zero:
            lean_unreachable(); // LCOV_EXCL_LINE
        case level_kind::Param:
            return format(param_id(l));
        case level_kind::Global:
            return format(global_id(l));
        case level_kind::Meta:
            return pp_meta(l);
        case level_kind::Succ: {
            auto p = to_offset(l);
            return pp_child(p.first) + format("+") + format(p.second);
        }
        case level_kind::Max: case level_kind::IMax:
            return pp_max(l);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

bool pretty_fn::is_implicit(expr const & f) {
    // Remark: we assume preterms do not have implicit arguments,
    // since they have not been elaborated yet.
    // Moreover, the type checker will probably produce an error
    // when trying to infer type information
    if (m_implict || m_preterm)
        return false; // showing implicit arguments
    if (!closed(f)) {
        // the Lean type checker assumes expressions are closed.
        return false;
    }
    try {
        expr t = m_ctx.relaxed_whnf(m_ctx.infer(f));
        if (is_pi(t)) {
            binder_info bi = binding_info(t);
            return bi.is_implicit() || bi.is_strict_implicit() || bi.is_inst_implicit();
        } else {
            return false;
        }
    } catch (exception &) {
        return false;
    }
}

bool pretty_fn::is_prop(expr const & e) {
    try {
        if (!m_env.impredicative())
            return false;
        expr t = m_ctx.relaxed_whnf(m_ctx.infer(e));
        return t == mk_Prop();
    } catch (exception &) {
        return false;
    }
}

auto pretty_fn::add_paren_if_needed(result const & r, unsigned bp) -> result {
    if (r.rbp() < bp) {
        return result(paren(r.fmt()));
    } else {
        return r;
    }
}

auto pretty_fn::pp_child_core(expr const & e, unsigned bp, bool ignore_hide) -> result {
    return add_paren_if_needed(pp(e, ignore_hide), bp);
}

static expr consume_ref_annotations(expr const & e) {
    if (is_explicit(e))
        return consume_ref_annotations(get_explicit_arg(e));
    else
        return e;
}

enum local_ref_kind { LocalRef, OverridenLocalRef, NotLocalRef };

static local_ref_kind check_local_ref(environment const & env, expr const & e, unsigned & num_ref_univ_params) {
    expr const & rfn = get_app_fn(e);
    if (!is_constant(rfn))
        return NotLocalRef;
    auto ref = get_local_ref_info(env, const_name(rfn));
    if (!ref)
        return NotLocalRef;
    if (is_as_atomic(*ref))
        ref = get_as_atomic_arg(*ref);
    buffer<expr> ref_args, e_args;
    expr ref_fn = consume_ref_annotations(get_app_args(*ref, ref_args));
    get_app_args(e, e_args);
    if (!is_constant(ref_fn) || e_args.size() != ref_args.size()) {
        return NotLocalRef;
    }
    for (unsigned i = 0; i < e_args.size(); i++) {
        expr e_arg   = e_args[i];
        expr ref_arg = consume_ref_annotations(ref_args[i]);
        if (!is_local(e_arg) || !is_local(ref_arg) || local_pp_name(e_arg) != local_pp_name(ref_arg))
            return OverridenLocalRef;
    }
    num_ref_univ_params = length(const_levels(ref_fn));
    buffer<level> lvls;
    to_buffer(const_levels(rfn), lvls);
    if (lvls.size() < num_ref_univ_params) {
        return NotLocalRef;
    }
    for (unsigned i = 0; i < num_ref_univ_params; i++) {
        level const & l = lvls[i];
        if (!is_param(l)) {
            return OverridenLocalRef;
        }
        for (unsigned j = 0; j < i; j++)
            if (lvls[i] == lvls[j]) {
                return OverridenLocalRef;
            }
    }
    return LocalRef;
}

static bool is_local_ref(environment const & env, expr const & e) {
    unsigned num_ref_univ_params;
    return check_local_ref(env, e, num_ref_univ_params) == LocalRef;
}

auto pretty_fn::pp_overriden_local_ref(expr const & e) -> result {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    result res_fn;
    {
        flet<bool> set1(m_full_names, true);
        res_fn = pp_const(fn, some(0u));
    }
    format fn_fmt    = res_fn.fmt();
    if (const_name(fn).is_atomic())
        fn_fmt = compose(format("_root_."), fn_fmt);
    if (m_implict && has_implicit_args(fn))
        fn_fmt = compose(*g_explicit_fmt, fn_fmt);
    format r_fmt = fn_fmt;
    expr curr_fn = fn;
    for (unsigned i = 0; i < args.size(); i++) {
        expr const & arg = args[i];
        if (m_implict || !is_implicit(curr_fn)) {
            result res_arg   = pp_child(arg, max_bp());
            r_fmt = group(compose(r_fmt, nest(m_indent, compose(line(), res_arg.fmt()))));
        }
        curr_fn = mk_app(curr_fn, arg);
    }
    return result(max_bp()-1, r_fmt);
}

bool pretty_fn::ignore_local_ref(expr const & e) {
    expr const & fn = get_app_fn(e);
    return m_full_names && (!is_constant(fn) || !const_name(fn).is_atomic());
}

// Return some result if \c e is of the form (c p_1 ... p_n) where
// c is a constant, and p_i's are parameters fixed in a section.
auto pretty_fn::pp_local_ref(expr const & e) -> optional<result> {
    if (ignore_local_ref(e))
        return optional<result>();
    unsigned num_ref_univ_params;
    switch (check_local_ref(m_env, e, num_ref_univ_params)) {
    case NotLocalRef:
        return optional<result>();
    case LocalRef:
        return some(pp_const(get_app_fn(e), optional<unsigned>(num_ref_univ_params)));
    case OverridenLocalRef:
        return some(pp_overriden_local_ref(e));
    }
    lean_unreachable();
}

static bool is_coercion(expr const & e) {
    return is_app_of(e, get_coe_name()) && get_app_num_args(e) >= 4;
}

static bool is_coercion_fn(expr const & e) {
    return is_app_of(e, get_coe_fn_name()) && get_app_num_args(e) >= 3;
}

auto pretty_fn::pp_hide_coercion(expr const & e, unsigned bp, bool ignore_hide) -> result {
    lean_assert(is_coercion(e));
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() == 4) {
        return pp_child(args[3], bp, ignore_hide);
    } else {
        expr new_e = mk_app(args.size() - 3, args.data() + 3);
        return pp_child(new_e, bp, ignore_hide);
    }
}

auto pretty_fn::pp_hide_coercion_fn(expr const & e, unsigned bp, bool ignore_hide) -> result {
    lean_assert(is_coercion_fn(e));
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() == 3) {
        return pp_child(args[2], bp, ignore_hide);
    } else {
        expr new_e = mk_app(args.size() - 2, args.data() + 2);
        return pp_child(new_e, bp, ignore_hide);
    }
}

auto pretty_fn::pp_child(expr const & e, unsigned bp, bool ignore_hide) -> result {
    if (is_app(e)) {
        if (auto r = pp_local_ref(e))
            return add_paren_if_needed(*r, bp);
        if (m_numerals) {
            if (auto n = to_num(e)) return pp_num(*n);
            if (auto n = to_num_core(e)) return pp_num(*n);
        }
        if (m_strings) {
            if (auto r = to_string(e)) return pp_string_literal(*r);
            if (auto r = to_char(e)) return pp_char_literal(*r);
        }
        expr const & f = app_fn(e);
        if (is_implicit(f)) {
            return pp_child(f, bp, ignore_hide);
        } else if (!m_coercion && is_coercion(e)) {
            return pp_hide_coercion(e, bp, ignore_hide);
        } else if (!m_coercion && is_coercion_fn(e)) {
            return pp_hide_coercion_fn(e, bp, ignore_hide);
        }
    }
    return pp_child_core(e, bp, ignore_hide);
}

auto pretty_fn::pp_var(expr const & e) -> result {
    unsigned vidx = var_idx(e);
    return result(compose(format("#"), format(vidx)));
}

auto pretty_fn::pp_sort(expr const & e) -> result {
    level u = sort_level(e);
    if (u == mk_level_zero()) {
        return m_env.impredicative() ? result(format("Prop")) : result(format("Type"));
    } else if (m_env.impredicative() && u == mk_level_one()) {
        return result(format("Type"));
    } else {
        return result(group(format("Type") + space() + nest(5, pp_child(u))));
    }
}

optional<name> pretty_fn::is_aliased(name const & n) const {
    if (auto it = is_expr_aliased(m_env, n)) {
        // must check if we are not shadow by current namespace
        for (name const & ns : get_namespaces(m_env)) {
            if (!ns.is_anonymous() && m_env.find(ns + *it))
                return optional<name>();
        }
        return it;
    } else {
        return optional<name>();
    }
}

auto pretty_fn::pp_const(expr const & e, optional<unsigned> const & num_ref_univ_params) -> result {
    if (is_neutral_expr(e) && m_unicode)
        return format("◾");
    if (is_unreachable_expr(e) && m_unicode)
        return format("⊥");
    name n = const_name(e);
    if (m_notation && n == get_Unit_star_name())
        return format("()");
    if (!num_ref_univ_params) {
        if (auto r = pp_local_ref(e))
            return *r;
    }
    // Remark: if num_ref_univ_params is "some", then it contains the number of
    // universe levels that are fixed in a section. That is, \c e corresponds to
    // a constant in a section which has fixed levels.
    if (!m_full_names) {
        if (auto it = is_aliased(n)) {
            if (!m_private_names || !hidden_to_user_name(m_env, n))
                n = *it;
        } else {
            for (name const & ns : get_namespaces(m_env)) {
                if (!ns.is_anonymous()) {
                    name new_n = n.replace_prefix(ns, name());
                    if (new_n != n &&
                        !new_n.is_anonymous() &&
                        (!new_n.is_atomic() || !is_protected(m_env, n))) {
                        n = new_n;
                        break;
                    }
                }
            }
        }
    }
    if (!m_private_names) {
        if (auto n1 = hidden_to_user_name(m_env, n))
            n = *n1;
    }
    if (m_universes && !empty(const_levels(e))) {
        unsigned first_idx = 0;
        buffer<level> ls;
        to_buffer(const_levels(e), ls);
        if (num_ref_univ_params) {
            if (ls.size() <= *num_ref_univ_params)
                return result(format(n));
            else
                first_idx = *num_ref_univ_params;
        }
        format r = compose(format(n), format(".{"));
        bool first = true;
        for (unsigned i = first_idx; i < ls.size(); i++) {
            level const & l = ls[i];
            format l_fmt = pp_level(l);
            if (is_max(l) || is_imax(l))
                l_fmt = paren(l_fmt);
            if (first)
                r += nest(m_indent, l_fmt);
            else
                r += nest(m_indent, compose(line(), l_fmt));
            first = false;
        }
        r += format("}");
        return result(group(r));
    } else {
        return result(format(n));
    }
}

auto pretty_fn::pp_meta(expr const & e) -> result {
    if (is_idx_metavar(e)) {
        return result(format((sstream() << "?x_" << to_meta_idx(e)).str()));
    } else if (is_metavar_decl_ref(e) && !m_purify_metavars) {
        return result(format((sstream() << "?m_" << get_metavar_decl_ref_suffix(e)).str()));
    } else if (m_purify_metavars) {
        return result(compose(format("?"), format(mlocal_name(e))));
    } else {
        return result(compose(format("?M."), format(mlocal_name(e))));
    }
}

auto pretty_fn::pp_local(expr const & e) -> result {
    name n = sanitize_if_fresh(local_pp_name(e));
    if (m_locals_full_names)
        return result(format("<") + format(n + mlocal_name(e)) + format(">"));
    else
        return format(n);
}

bool pretty_fn::has_implicit_args(expr const & f) {
    if (!closed(f) || m_preterm) {
        // The Lean type checker assumes expressions are closed.
        // If preterms are being processed, then we assume
        // there are no implicit arguments.
        return false;
    }
    try {
        expr type = m_ctx.relaxed_whnf(m_ctx.infer(f));
        push_local_fn push_local(m_ctx);
        while (is_pi(type)) {
            binder_info bi = binding_info(type);
            if (bi.is_implicit() || bi.is_strict_implicit() || bi.is_inst_implicit())
                return true;
            expr local = push_local(binding_name(type), binding_domain(type), binding_info(type));
            type = m_ctx.relaxed_whnf(instantiate(binding_body(type), local));
        }
        return false;
    } catch (exception &) {
        return false;
    }
}

auto pretty_fn::pp_app(expr const & e) -> result {
    if (auto r = pp_local_ref(e))
        return *r;
    expr const & fn = app_fn(e);
    // If the application contains a metavariable, then we want to
    // show the function, otherwise it would be hard to understand the
    // context where the metavariable occurs. This is hack to implement
    // formatter.hide_full_terms
    bool ignore_hide = true;
    result res_fn    = pp_child(fn, max_bp()-1, ignore_hide);
    format fn_fmt    = res_fn.fmt();
    if (m_implict && (!is_app(fn) || (!ignore_local_ref(fn) && is_local_ref(m_env, fn))) && has_implicit_args(fn))
        fn_fmt = compose(*g_explicit_fmt, fn_fmt);
    result res_arg = pp_child(app_arg(e), max_bp());
    return result(max_bp()-1, group(compose(fn_fmt, nest(m_indent, compose(line(), res_arg.fmt())))));
}

format pretty_fn::pp_binder(expr const & local) {
    format r;
    auto bi = local_info(local);
    if (bi != binder_info())
        r += format(open_binder_string(bi, m_unicode));
    r += format(local_pp_name(local));
    if (m_binder_types) {
        r += space();
        r += compose(colon(), nest(m_indent, compose(line(), pp_child(mlocal_type(local), 0).fmt())));
    }
    if (bi != binder_info())
        r += format(close_binder_string(bi, m_unicode));
    return r;
}

format pretty_fn::pp_binder_block(buffer<name> const & names, expr const & type, binder_info const & bi) {
    format r;
    if (m_binder_types || bi != binder_info())
        r += format(open_binder_string(bi, m_unicode));
    for (name const & n : names) {
        r += format(n);
    }
    if (m_binder_types) {
        r += space();
        r += compose(colon(), nest(m_indent, compose(line(), pp_child(type, 0).fmt())));
    }
    if (m_binder_types || bi != binder_info())
        r += format(close_binder_string(bi, m_unicode));
    return group(r);
}

format pretty_fn::pp_binders(buffer<expr> const & locals) {
    unsigned num     = locals.size();
    buffer<name> names;
    expr local       = locals[0];
    expr   type      = mlocal_type(local);
    binder_info bi   = local_info(local);
    names.push_back(local_pp_name(local));
    format r;
    for (unsigned i = 1; i < num; i++) {
        expr local = locals[i];
        if (!bi.is_inst_implicit() && mlocal_type(local) == type && local_info(local) == bi) {
            names.push_back(local_pp_name(local));
        } else {
            r += group(compose(line(), pp_binder_block(names, type, bi)));
            names.clear();
            type = mlocal_type(local);
            bi   = local_info(local);
            names.push_back(local_pp_name(local));
        }
    }
    r += group(compose(line(), pp_binder_block(names, type, bi)));
    return r;
}

auto pretty_fn::pp_lambda(expr const & e) -> result {
    expr b = e;
    buffer<expr> locals;
    while (is_lambda(b)) {
        auto p = binding_body_fresh(b, true);
        locals.push_back(p.second);
        b = p.first;
    }
    format r = m_unicode ? *g_lambda_n_fmt : *g_lambda_fmt;
    r += pp_binders(locals);
    r += group(compose(comma(), nest(m_indent, compose(line(), pp_child(b, 0).fmt()))));
    return result(0, r);
}

/** \brief Similar to #is_arrow, but only returns true if binder_info is the default one.
    That is, we don't want to lose binder info when pretty printing.
*/
static bool is_default_arrow(expr const & e) {
    return is_arrow(e) && binding_info(e) == binder_info();
}

auto pretty_fn::pp_pi(expr const & e) -> result {
    if (is_default_arrow(e)) {
        result lhs = pp_child(binding_domain(e), get_arrow_prec());
        expr   b   = lift_free_vars(binding_body(e), 1);
        result rhs = is_pi(b) ? pp(b) : pp_child(b, get_arrow_prec()-1);
        format r   = group(lhs.fmt() + space() + (m_unicode ? *g_arrow_n_fmt : *g_arrow_fmt) + line() + rhs.fmt());
        return result(get_arrow_prec(), get_arrow_prec()-1, r);
    } else {
        expr b = e;
        buffer<expr> locals;
        while (is_pi(b) && !is_default_arrow(b)) {
            auto p = binding_body_fresh(b, true);
            locals.push_back(p.second);
            b = p.first;
        }
        format r;
        if (is_prop(b))
            r = m_unicode ? *g_forall_n_fmt : *g_forall_fmt;
        else
            r = m_unicode ? *g_pi_n_fmt : *g_pi_fmt;
        r += pp_binders(locals);
        r += group(compose(comma(), nest(m_indent, compose(line(), pp_child(b, 0).fmt()))));
        return result(0, r);
    }
}

static bool is_have(expr const & e) {
    return is_app(e) && is_have_annotation(app_fn(e)) && is_binding(get_annotation_arg(app_fn(e)));
}
static bool is_show(expr const & e) {
    return is_show_annotation(e) && is_app(get_annotation_arg(e)) &&
        is_lambda(app_fn(get_annotation_arg(e)));
}

auto pretty_fn::pp_have(expr const & e) -> result {
    expr proof   = app_arg(e);
    expr binding = get_annotation_arg(app_fn(e));
    auto p       = binding_body_fresh(binding, true);
    expr local   = p.second;
    expr body    = p.first;
    name const & n = local_pp_name(local);
    format type_fmt  = pp_child(mlocal_type(local), 0).fmt();
    format proof_fmt = pp_child(proof, 0).fmt();
    format body_fmt  = pp_child(body, 0).fmt();
    format head_fmt  = *g_have_fmt;
    format r = head_fmt + space() + format(n) + space();
    r += colon() + nest(m_indent, line() + type_fmt + comma() + space() + *g_from_fmt);
    r = group(r);
    r += nest(m_indent, line() + proof_fmt + comma());
    r = group(r);
    r += line() + body_fmt;
    return result(0, r);
}

auto pretty_fn::pp_show(expr const & e) -> result {
    lean_assert(is_show(e));
    expr s           = get_annotation_arg(e);
    expr proof       = app_arg(s);
    expr type        = binding_domain(app_fn(s));
    format type_fmt  = pp_child(type, 0).fmt();
    format proof_fmt = pp_child(proof, 0).fmt();
    format r = *g_show_fmt + space() + nest(5, type_fmt) + comma() + space() + *g_from_fmt;
    r = group(r);
    r += nest(m_indent, compose(line(), proof_fmt));
    return result(0, group(r));
}

auto pretty_fn::pp_explicit(expr const & e) -> result {
    result res_arg = pp_child(get_explicit_arg(e), max_bp());
    return result(max_bp(), compose(*g_explicit_fmt, res_arg.fmt()));
}

auto pretty_fn::pp_delayed_abstraction(expr const & e) -> result {
    if (m_delayed_abstraction) {
        format r = format("delayed[");
        r += pp(get_delayed_abstraction_expr(e)).fmt();
        r += format("]");
        return result(r);
    } else {
        return pp(get_delayed_abstraction_expr(e));
    }
}

auto pretty_fn::pp_equation(expr const & e) -> format {
    lean_assert(is_equation(e));
    format r = format("|");
    buffer<expr> args;
    get_app_args(equation_lhs(e), args);
    for (expr const & arg : args) {
        r += space() + pp_child(arg, max_bp()).fmt();
    }
    r += space() + *g_assign_fmt + space() + pp_child(equation_rhs(e), 0).fmt();
    return r;
}

auto pretty_fn::pp_equations(expr const & e) -> optional<result> {
    buffer<expr> eqns;
    unsigned num_fns = equations_num_fns(e);
    to_equations(e, eqns);
    buffer<expr> fns;
    expr eqn = eqns[0];
    for (unsigned i = 0; i < num_fns; i++) {
        if (!is_lambda(eqn)) return optional<result>();
        if (!closed(binding_domain(eqn))) return optional<result>();
        auto p = binding_body_fresh(eqn, true);
        fns.push_back(p.second);
        eqn = p.first;
    }
    format r;
    if (num_fns > 1) {
        r = format("mutual_def") + space();
        for (unsigned i = 0; i < num_fns; i++) {
            if (i > 0) r += format(", ");
            r += pp(fns[i]).fmt();
        }
        r += line();
    } else {
        r = format("def") + space() + pp(fns[0]).fmt() + space() + colon() + space() + pp(mlocal_type(fns[0])).fmt();
    }
    unsigned eqnidx = 0;
    for (unsigned fidx = 0; fidx < num_fns; fidx++) {
        if (num_fns > 1) {
            r += format("with") + space() + pp(fns[fidx]).fmt() + space() + colon() +
                space() + pp(mlocal_type(fns[fidx])).fmt();
        }
        if (eqnidx >= eqns.size()) return optional<result>();
        expr eqn = eqns[eqnidx];
        while (is_lambda(eqn)) {
            eqn = binding_body_fresh(eqn, true).first;
        }
        eqnidx++;
        if (is_equation(eqn)) {
            r += line() + pp_equation(eqn);
            while (eqnidx < eqns.size()) {
                expr eqn = eqns[eqnidx];
                while (is_lambda(eqn)) {
                    eqn = binding_body_fresh(eqn, true).first;
                }
                if (is_equation(eqn) &&
                    get_app_fn(equation_lhs(eqn)) == fns[fidx]) {
                    r += line() + pp_equation(eqn);
                    eqnidx++;
                } else {
                    break;
                }
            }
        } else {
            /* noequation */
            r += line() + format("[none]");
        }
    }
    if (eqns.size() != eqnidx) return optional<result>();
    return optional<result>(r);
}

auto pretty_fn::pp_macro_default(expr const & e) -> result {
    // TODO(Leo): have macro annotations
    // fix macro<->pp interface
    format r = compose(format("["), format(macro_def(e).get_name()));
    for (unsigned i = 0; i < macro_num_args(e); i++)
        r += nest(m_indent, compose(line(), pp_child(macro_arg(e, i), max_bp()).fmt()));
    r += format("]");
    return result(group(r));
}

auto pretty_fn::pp_macro(expr const & e) -> result {
    if (is_explicit(e)) {
        return pp_explicit(e);
    } else if (is_quote(e)) {
        return result(format("`(") + nest(2, pp(get_quote_expr(e)).fmt()) + format(")"));
    } else if (is_delayed_abstraction(e)) {
        return pp_delayed_abstraction(e);
    } else if (is_inaccessible(e)) {
        format r = format(".") + pp_child(get_annotation_arg(e), max_bp()).fmt();
        return result(r);
        // } else if (is_pattern_hint(e)) {
        // return result(group(nest(2, format("(:") + pp(get_pattern_hint_arg(e)).fmt() + format(":)"))));
    } else if (is_marked_as_comp_irrelevant(e)) {
        if (m_hide_comp_irrel)
            return m_unicode ? format("◾") : format("irrel");
        else
            return pp(get_annotation_arg(e));
    } else if (!m_strings && to_string(e)) {
        expr n = *macro_def(e).expand(e, m_ctx);
        return pp(n);
    } else if (is_equations(e)) {
        if (auto r = pp_equations(e))
            return *r;
        else
            return pp_macro_default(e);
    } else if (is_annotation(e)) {
        return pp(get_annotation_arg(e));
    } else if (is_rec_fn_macro(e)) {
        return format("[") + format(get_rec_fn_name(e)) + format("]");
    } else {
        return pp_macro_default(e);
    }
}

auto pretty_fn::pp_let(expr e) -> result {
    buffer<std::tuple<expr, expr, expr>> decls;
    while (true) {
        expr t   = let_type(e);
        expr v   = let_value(e);
        expr b   = let_body(e);
        auto p   = let_body_fresh(e, true);
        decls.emplace_back(p.second, t, v);
        e        = p.first;
        if (!is_let(e))
            break;
    }
    lean_assert(!decls.empty());
    format r    = *g_let_fmt;
    unsigned sz = decls.size();
    for (unsigned i = 0; i < sz; i++) {
        expr l, t, v;
        std::tie(l, t, v) = decls[i];
        name const & n = local_pp_name(l);
        format beg     = i == 0 ? space() : line();
        format sep     = i < sz - 1 ? comma() : format();
        format entry   = format(n);
        format v_fmt   = pp_child(v, 0).fmt();
        if (is_neutral_expr(t)) {
            entry += space() + *g_assign_fmt + nest(m_indent, line() + v_fmt + sep);
        } else {
            format t_fmt   = pp_child(t, 0).fmt();
            entry += space() + colon() + space() + t_fmt + space() + *g_assign_fmt + nest(m_indent, line() + v_fmt + sep);
        }
        r += nest(3 + 1, beg + group(entry));
    }
    format b = pp_child(e, 0).fmt();
    r += line() + *g_in_fmt + space() + nest(2 + 1, b);
    return result(0, r);
}

auto pretty_fn::pp_num(mpz const & n) -> result {
    return result(format(n));
}

// Return the number of parameters in a notation declaration.
static unsigned get_num_parameters(notation_entry const & entry) {
    if (entry.is_numeral())
        return 0;
    unsigned r = 0;
    if (!entry.is_nud())
        r++;
    for (auto const & t : entry.get_transitions()) {
        switch (t.get_action().kind()) {
        case notation::action_kind::Skip:
        case notation::action_kind::Binder:
        case notation::action_kind::Binders:
            break;
        case notation::action_kind::Expr:
        case notation::action_kind::Exprs:
        case notation::action_kind::ScopedExpr:
        case notation::action_kind::Ext:
            r++;
        }
    }
    return r;
}

bool pretty_fn::match(level const & p, level const & l) {
    if (p == l)
        return true;
    if (m_universes)
        return false;
    if (is_placeholder(p))
        return true;
    if (is_succ(p) && is_succ(l))
        return match(succ_of(p), succ_of(l));
    return false;
}

bool pretty_fn::match(expr const & p, expr const & e, buffer<optional<expr>> & args) {
    if (is_explicit(p)) {
        return match(get_explicit_arg(p), e, args);
    } else if (is_as_atomic(p)) {
        return match(get_app_fn(get_as_atomic_arg(p)), e, args);
    } else if (is_var(p)) {
        unsigned vidx = var_idx(p);
        if (vidx >= args.size())
            return false;
        unsigned i = args.size() - vidx - 1;
        if (args[i])
            return *args[i] == e;
        args[i] = e;
        return true;
    } else if (is_placeholder(p)) {
        return true;
    } else if (is_constant(p) && is_constant(e)) {
        if (const_name(p) != const_name(e))
            return false;
        levels p_ls = const_levels(p);
        levels e_ls = const_levels(p);
        while (!is_nil(p_ls)) {
            if (is_nil(e_ls))
                return false; // e must have at least as many arguments as p
            if (!match(head(p_ls), head(e_ls)))
                return false;
            p_ls = tail(p_ls);
            e_ls = tail(e_ls);
        }
        return true;
    } else if (is_sort(p)) {
        if (!is_sort(e))
            return false;
        return match(sort_level(p), sort_level(e));
    } else if (is_app(e)) {
        buffer<expr> p_args, e_args;
        expr p_fn    = get_app_args(p, p_args);
        expr e_fn    = get_app_args(e, e_args);
        if (!match(p_fn, e_fn, args))
            return false;
        if (is_explicit(p)) {
            if (p_args.size() != e_args.size())
                return false;
            for (unsigned i = 0; i < p_args.size(); i++) {
                if (!match(p_args[i], e_args[i], args))
                    return false;
            }
            return true;
        } else {
            try {
                expr fn_type = m_ctx.infer(e_fn);
                unsigned j = 0;
                for (unsigned i = 0; i < e_args.size(); i++) {
                    fn_type = m_ctx.relaxed_whnf(fn_type);
                    if (!is_pi(fn_type))
                        return false;
                    expr const & body        = binding_body(fn_type);
                    binder_info const & info = binding_info(fn_type);
                    if ((closed(body)) && is_explicit(info)) {
                        if (j >= p_args.size())
                            return false;
                        if (!match(p_args[j], e_args[i], args))
                            return false;
                        j++;
                    }
                    fn_type = instantiate(body, e_args[i]);
                }
                return j == p_args.size();
            } catch (exception &) {
                return false;
            }
        }
    } else {
        return false;
    }
}

static unsigned get_some_precedence(token_table const & t, name const & tk) {
    if (tk.is_atomic() && tk.is_string()) {
        if (auto p = get_expr_precedence(t, tk.get_string()))
            return *p;
    } else {
        if (auto p = get_expr_precedence(t, tk.to_string().c_str()))
            return *p;
    }
    return 0;
}

auto pretty_fn::pp_notation_child(expr const & e, unsigned lbp, unsigned rbp) -> result {
    if (is_app(e)) {
        if (m_numerals) {
            if (auto n = to_num(e)) return pp_num(*n);
            if (auto n = to_num_core(e)) return pp_num(*n);
        }
        if (m_strings) {
            if (auto r = to_string(e)) return pp_string_literal(*r);
        }
        expr const & f = app_fn(e);
        if (is_implicit(f)) {
            return pp_notation_child(f, lbp, rbp);
        } else if (!m_coercion && is_coercion(e)) {
            return pp_hide_coercion(e, rbp);
        } else if (!m_coercion && is_coercion_fn(e)) {
            return pp_hide_coercion_fn(e, rbp);
        }
    }
    result r = pp(e);
    if (r.rbp() < lbp || r.lbp() <= rbp) {
        return result(paren(r.fmt()));
    } else {
        return r;
    }
}

static bool is_atomic_notation(notation_entry const & entry) {
    if (!entry.is_nud())
        return false;
    list<notation::transition> const & ts = entry.get_transitions();
    if (!is_nil(tail(ts)))
        return false;
    return head(ts).get_action().kind() == notation::action_kind::Skip;
}

auto pretty_fn::pp_notation(notation_entry const & entry, buffer<optional<expr>> & args) -> optional<result> {
    if (entry.is_numeral()) {
        return some(result(format(entry.get_num())));
    } else if (is_atomic_notation(entry)) {
        format fmt   = format(head(entry.get_transitions()).get_token());
        return some(result(fmt));
    } else {
        using notation::transition;
        buffer<transition> ts;
        buffer<expr> locals; // from scoped_expr
        to_buffer(entry.get_transitions(), ts);
        format fmt;
        unsigned i         = ts.size();
        unsigned last_rbp  = inf_bp()-1;
        unsigned token_lbp = 0;
        bool last          = true;
        while (i > 0) {
            --i;
            format curr;
            notation::action const & a = ts[i].get_action();
            name const & tk = ts[i].get_token();
            format tk_fmt = format(ts[i].get_pp_token());
            switch (a.kind()) {
            case notation::action_kind::Skip:
                curr = tk_fmt;
                if (last)
                    last_rbp = inf_bp();
                break;
            case notation::action_kind::Expr:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    expr e = *args.back();
                    args.pop_back();
                    result e_r   = pp_notation_child(e, token_lbp, a.rbp());
                    curr = tk_fmt + e_r.fmt();
                    if (last)
                        last_rbp = a.rbp();
                    break;
                }
            case notation::action_kind::Exprs:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    expr e = *args.back();
                    args.pop_back();
                    expr const & rec = a.get_rec();
                    optional<expr> const & ini = a.get_initial();
                    buffer<expr> rec_args;
                    bool matched_once = false;
                    while (true) {
                        args.resize(args.size() + 2);
                        if (!match(rec, e, args)) {
                            args.pop_back();
                            args.pop_back();
                            break;
                        }
                        optional<expr> new_e = args.back();
                        args.pop_back();
                        optional<expr> rec_arg = args.back();
                        args.pop_back();
                        if (!new_e || !rec_arg)
                            return optional<result>();
                        rec_args.push_back(*rec_arg);
                        e = *new_e;
                        matched_once = true;
                    }
                    if (!matched_once && ini)
                        return optional<result>();
                    if (ini) {
                        if (!match(*ini, e, args))
                            return optional<result>();
                    } else {
                        rec_args.push_back(e);
                    }
                    if (!a.is_fold_right())
                        std::reverse(rec_args.begin(), rec_args.end());
                    unsigned curr_lbp = token_lbp;
                    if (auto t = a.get_terminator()) {
                        curr = format(*t);
                        curr_lbp = get_some_precedence(m_token_table, *t);
                    }
                    unsigned j       = rec_args.size();
                    format sep_fmt   = format(a.get_sep());
                    unsigned sep_lbp = get_some_precedence(m_token_table, a.get_sep());
                    while (j > 0) {
                        --j;
                        result arg_res = pp_notation_child(rec_args[j], curr_lbp, a.rbp());
                        if (j == 0) {
                            curr = tk_fmt + arg_res.fmt() + curr;
                        } else {
                            curr = sep_fmt + arg_res.fmt() + curr;
                        }
                        curr_lbp = sep_lbp;
                    }
                    break;
                }
            case notation::action_kind::Binder:
                if (locals.size() != 1)
                    return optional<result>();
                curr = tk_fmt + pp_binder(locals[0]);
                break;
            case notation::action_kind::Binders:
                curr = tk_fmt + pp_binders(locals);
                break;
            case notation::action_kind::ScopedExpr:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    expr e            = *args.back();
                    bool first_scoped = locals.empty();
                    unsigned i = 0;
                    args.pop_back();
                    expr const & rec = a.get_rec();
                    while (true) {
                        args.resize(args.size() + 1);
                        if (!match(rec, e, args) || !args.back()) {
                            args.pop_back();
                            break;
                        }
                        expr b = *args.back();
                        args.pop_back();
                        if (!((is_lambda(b) && a.use_lambda_abstraction()) ||
                              (is_pi(b) && !a.use_lambda_abstraction()))) {
                            break;
                        }
                        auto p = binding_body_fresh(b, true);
                        if (first_scoped) {
                            locals.push_back(p.second);
                        } else {
                            if (i >= locals.size() || locals[i] != p.second)
                                return optional<result>();
                        }
                        e = p.first;
                        i++;
                    }
                    if (locals.empty())
                        return optional<result>();
                    result e_r   = pp_notation_child(e, token_lbp, a.rbp());
                    curr = tk_fmt + e_r.fmt();
                    if (last)
                        last_rbp = a.rbp();
                    break;
                }
            case notation::action_kind::Ext:
                return optional<result>();
            }
            token_lbp = get_some_precedence(m_token_table, tk);
            if (last) {
                fmt = curr;
                last = false;
            } else {
                fmt = curr + fmt;
            }
        }
        unsigned first_lbp = inf_bp();
        if (!entry.is_nud()) {
            first_lbp = token_lbp;
            lean_assert(!last);
            if (args.size() != 1 || !args.back())
                return optional<result>();
            expr e = *args.back();
            args.pop_back();
            format e_fmt = pp_notation_child(e, token_lbp, 0).fmt();
            fmt = e_fmt + fmt;
        }
        return optional<result>(result(first_lbp, last_rbp, fmt));
    }
}

auto pretty_fn::pp_notation(expr const & e) -> optional<result> {
    if (!m_notation || is_var(e))
        return optional<result>();
    for (notation_entry const & entry : get_notation_entries(m_env, head_index(e))) {
        if (entry.group() == notation_entry_group::Reserve)
            continue;
        if (!m_unicode && !entry.is_safe_ascii())
            continue; // ignore this notation declaration since unicode support is not enabled
        unsigned num_params = get_num_parameters(entry);
        buffer<optional<expr>> args;
        args.resize(num_params);
        if (match(entry.get_expr(), e, args)) {
            if (auto r = pp_notation(entry, args))
                return r;
        }
    }
    return optional<result>();
}

static bool is_pp_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::App:
    case expr_kind::Lambda:
    case expr_kind::Pi:
    case expr_kind::Macro:
        return false;
    default:
        return true;
    }
}

/* Returns the theorem type if `e` is a proof and `m_proofs` is set to false. */
optional<expr> pretty_fn::is_proof(expr const & e) {
    if (m_proofs)
        return none_expr(); // showing proof terms
    if (!closed(e))
        // the Lean type checker assumes expressions are closed.
        return none_expr();
    try {
        expr t = m_ctx.infer(e);
        if (is_prop(t))
            return some_expr(head_beta_reduce(t));
        else
            return none_expr();
    } catch (exception &) {
        return none_expr();
    }
}

auto pretty_fn::pp_proof_type(expr const & t) -> result {
    format li = m_unicode ? format("⌞") : format("[proof ");
    format ri = m_unicode ? format("⌟") : format("]");
    return result(group(nest(1, li + pp(t).fmt() + ri)));
}

auto pretty_fn::pp(expr const & e, bool ignore_hide) -> result {
    check_system("pretty printer");
    if ((m_depth >= m_max_depth ||
         m_num_steps > m_max_steps ||
         (m_hide_full_terms && !ignore_hide && !has_expr_metavar(e))) &&
        !is_pp_atomic(e)) {
        return result(m_unicode ? *g_ellipsis_n_fmt : *g_ellipsis_fmt);
    }
    flet<unsigned> let_d(m_depth, m_depth+1);
    m_num_steps++;

    if (m_numerals) {
        if (auto n = to_num(e)) return pp_num(*n);
        if (auto n = to_num_core(e)) return pp_num(*n);
    }
    if (m_strings) {
        if (auto r = to_string(e)) return pp_string_literal(*r);
    }
    if (auto t = is_proof(e)) {
        return pp_proof_type(*t);
    }

    if (auto r = pp_notation(e))
        return *r;

    if (is_placeholder(e))  return result(*g_placeholder_fmt);
    if (is_show(e))         return pp_show(e);
    if (is_have(e))         return pp_have(e);
    if (is_typed_expr(e))   return pp(get_typed_expr_expr(e));
    if (m_num_nat_coe)
        if (auto k = to_unsigned(e))
            return format(*k);
    switch (e.kind()) {
    case expr_kind::Var:       return pp_var(e);
    case expr_kind::Sort:      return pp_sort(e);
    case expr_kind::Constant:  return pp_const(e);
    case expr_kind::Meta:      return pp_meta(e);
    case expr_kind::Local:     return pp_local(e);
    case expr_kind::App:       return pp_app(e);
    case expr_kind::Lambda:    return pp_lambda(e);
    case expr_kind::Pi:        return pp_pi(e);
    case expr_kind::Macro:     return pp_macro(e);
    case expr_kind::Let:       return pp_let(e);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

pretty_fn::pretty_fn(environment const & env, options const & o, abstract_type_context & ctx):
    m_env(env), m_ctx(ctx), m_token_table(get_token_table(env)) {
    set_options_core(o);
    m_meta_prefix   = "M";
    m_next_meta_idx = 1;
}

// Custom beta reduction procedure for the pretty printer.
// We don't want to reduce application in show annotations.
class pp_beta_reduce_fn : public replace_visitor {
    virtual expr visit_meta(expr const & e) override { return e; }
    virtual expr visit_local(expr const & e) override { return e; }

    virtual expr visit_macro(expr const & e) override {
        if (is_show_annotation(e) && is_app(get_annotation_arg(e))) {
            expr const & n = get_annotation_arg(e);
            expr new_fn  = visit(app_fn(n));
            expr new_arg = visit(app_arg(n));
            return mk_show_annotation(mk_app(new_fn, new_arg));
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

    virtual expr visit_app(expr const & e) override {
        expr new_e = replace_visitor::visit_app(e);
        if (is_head_beta(new_e))
            return visit(head_beta_reduce(new_e));
        else
            return new_e;
    }
};

std::string sexpr_to_string(sexpr const & s) {
    if (is_string(s))
        return to_string(s);
    std::stringstream ss;
    ss << s;
    return ss.str();
}

// check whether a space must be inserted between the strings so that lexing them would
// produce separate tokens
std::pair<bool, token_table const *> pretty_fn::needs_space_sep(token_table const * last, std::string const & s1, std::string const & s2) const {
    if (is_id_rest(get_utf8_last_char(s1.data()), s1.data() + s1.size()) && is_id_rest(s2.data(), s2.data() + s2.size()))
        return mk_pair(true, nullptr); // would be lexed as a single identifier without space

    if (last) {
        // complete deferred two-token lookahead
        for (char c : s2) {
            last = last->find(c);
            if (!last)
                break;
            if (last->value())
                return mk_pair(true, nullptr);
        }
        if (last) {
            // would need an even larger lookahead, give up
            return mk_pair(true, nullptr);
        }
    }

    // check whether s1 + s2 has a longer prefix in the token table than s1
    token_table const * t = &m_token_table;
    for (char c : s1) {
        t = t->find(c);
        if (!t)
            return mk_pair(false, nullptr); // s1 must be an identifier, and we know s2 does not start with is_id_rest
    }
    for (char c : s2) {
        t = t->find(c);
        if (!t)
            return mk_pair(false, nullptr);
        if (t->value())
            return mk_pair(true, nullptr);
    }

    // the next identifier may expand s1 + s2 to a token, defer decision
    return mk_pair(false, t);
}

format pretty_fn::operator()(expr const & e) {
    m_depth = 0; m_num_steps = 0;
    result r;
    if (m_beta)
        r = pp_child(purify(pp_beta_reduce_fn()(e)), 0);
    else
        r = pp_child(purify(e), 0);

    // insert spaces so that lexing the result round-trips
    std::function<bool(sexpr const &, sexpr const &)> sep; // NOLINT
    token_table const * last = nullptr;
    sep = [&](sexpr const & s1, sexpr const & s2) {
        bool b;
        std::tie(b, last) = needs_space_sep(last, sexpr_to_string(s1), sexpr_to_string(s2));
        return b;
    };
    return r.fmt().separate_tokens(sep);
}

formatter_factory mk_pretty_formatter_factory() {
    return [](environment const & env, options const & o, abstract_type_context & ctx) { // NOLINT
        auto fn_ptr = std::make_shared<pretty_fn>(env, o, ctx);
        return formatter(o, [=](expr const & e, options const & new_o) {
                fn_ptr->set_options(new_o);
                return (*fn_ptr)(e);
            });
    };
}

static options mk_options(bool detail) {
    options opts;
    if (detail) {
        opts = opts.update(name{"pp", "implicit"}, true);
        opts = opts.update(name{"pp", "notation"}, false);
    }
    return opts;
}

static void pp_core(environment const & env, expr const & e, bool detail) {
    type_checker tc(env);
    io_state ios(mk_pretty_formatter_factory(), mk_options(detail));
    regular(env, ios, tc) << e << "\n";
}

/* static void pp_core(environment const & env, goal const & g, bool detail) {
    type_checker tc(env);
    io_state ios(mk_pretty_formatter_factory(), mk_options(detail));
    regular(env, ios, tc) << g << "\n";
}

static void pp_core(environment const & env, proof_state const & s, bool detail) {
    type_checker tc(env);
    io_state ios(mk_pretty_formatter_factory(), mk_options(detail));
    auto out = regular(env, ios, tc);
    out << s.pp(out.get_formatter()) << "\n";
}
*/

}
// for debugging purposes
void pp(lean::environment const & env, lean::expr const & e) { lean::pp_core(env, e, false); }
// void pp(lean::environment const & env, lean::goal const & g) { lean::pp_core(env, g, false); }
// void pp(lean::environment const & env, lean::proof_state const & s) { lean::pp_core(env, s, false); }
void pp_detail(lean::environment const & env, lean::expr const & e) { lean::pp_core(env, e, true); }
// void pp_detail(lean::environment const & env, lean::goal const & g) { lean::pp_core(env, g, true); }
// void pp_detail(lean::environment const & env, lean::proof_state const & s) { lean::pp_core(env, s, true); }
