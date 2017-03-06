/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/pattern_attribute.h"
#include "library/app_builder.h"
#include "library/replace_visitor_with_tc.h"
#include "library/equations_compiler/equations.h"
#include "library/equations_compiler/util.h"
#include "library/equations_compiler/primitive_rec.h"
#include "library/equations_compiler/elim_match.h"

namespace lean {
#define trace_primrec(Code) lean_trace(name({"eqn_compiler", "primitive_rec"}), type_context ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)
#define trace_primrec_aux(Code) lean_trace(name({"eqn_compiler", "primitive_rec"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); Code)
#define trace_debug_primrec(Code) lean_trace(name({"debug", "eqn_compiler", "primitive_rec"}), type_context ctx = mk_type_context(); scope_trace_env _scope1(m_env, ctx); Code)
#define trace_debug_primrec_aux(Code) lean_trace(name({"debug", "eqn_compiler", "primitive_rec"}), scope_trace_env _scope1(m_ctx.env(), m_ctx); Code)

struct primitive_rec_fn {
    environment      m_env;
    options          m_opts;
    metavar_context  m_mctx;
    local_context    m_lctx;

    expr             m_ref;
    equations_header m_header;
    unsigned         m_arg_pos;
    bool             m_reflexive;
    buffer<unsigned> m_indices_pos;

    primitive_rec_fn(environment const & env, options const & opts,
                      metavar_context const & mctx, local_context const & lctx):
        m_env(env), m_opts(opts), m_mctx(mctx), m_lctx(lctx) {
    }

    [[ noreturn ]] void throw_error(char const * msg) {
        throw generic_exception(m_ref, msg);
    }

    [[ noreturn ]] void throw_error(sstream const & strm) {
        throw generic_exception(m_ref, strm);
    }

    type_context mk_type_context() {
        return type_context(m_env, m_opts, m_mctx, m_lctx, transparency_mode::Semireducible);
    }

    environment const & env() const { return m_env; }
    metavar_context const & mctx() const { return m_mctx; }

    /** \brief Auxiliary object for checking whether recursive application are
        using an argument of the corresponding argument in equation left hand side. */
    struct check_rhs_fn {
        type_context & m_ctx;
        expr           m_lhs;
        expr           m_fn;
        expr           m_pattern;
        unsigned       m_arg_idx;

        check_rhs_fn(type_context & ctx, expr const & lhs, expr const & fn, expr const & pattern, unsigned arg_idx):
            m_ctx(ctx), m_lhs(lhs), m_fn(fn), m_pattern(pattern), m_arg_idx(arg_idx) {}

        bool is_constructor(expr const & e) const {
            return is_constant(e) && inductive::is_intro_rule(m_ctx.env(), const_name(e));
        }

        expr whnf(expr const & e) {
            /* We only unfold patterns and reducible definitions */
            return m_ctx.whnf_transparency_pred(e, [&](name const & n) {
                    return
                        has_pattern_attribute(m_ctx.env(), n) ||
                        is_reducible(m_ctx.env(), n);
                });
        }

        /** Return true iff \c s is an argument of \c t */
        bool is_rec_arg_of(expr s, expr t) {
            s = whnf(s);
            t = whnf(t);
            if (is_app(s)) {
                /* Support for reflexive inductive types */
                expr const & s_fn = get_app_fn(s);
                if (!is_constructor(s_fn))
                    return is_rec_arg_of(s_fn, t);
            }
            buffer<expr> t_args;
            expr const & t_fn = get_app_args(t, t_args);
            if (!is_constructor(t_fn))
                return false;
            return std::any_of(t_args.begin(), t_args.end(),
                               [&](expr const & t_arg) { return m_ctx.is_def_eq(s, t_arg); });
        }

        bool check_rhs(expr const & e) {
            switch (e.kind()) {
            case expr_kind::Var:   case expr_kind::Meta:
            case expr_kind::Local: case expr_kind::Constant:
            case expr_kind::Sort:
                return true;
            case expr_kind::Macro:
                for (unsigned i = 0; i < macro_num_args(e); i++)
                    if (!check_rhs(macro_arg(e, i)))
                        return false;
                return true;
            case expr_kind::App: {
                buffer<expr> args;
                expr const & fn = get_app_args(e, args);
                if (!check_rhs(fn))
                    return false;
                for (unsigned i = 0; i < args.size(); i++)
                    if (!check_rhs(args[i]))
                        return false;
                if (is_local(fn) && mlocal_name(fn) == mlocal_name(m_fn)) {
                    /* recusive application */
                    if (m_arg_idx < args.size()) {
                        expr const & arg = args[m_arg_idx];
                        if (!is_rec_arg_of(arg, m_pattern)) {
                            trace_primrec_aux(tout() << "primitive recursion on argument #" << (m_arg_idx+1)
                                          << " was not used "
                                          << "for '" << m_fn << "'\nargument #" << (m_arg_idx+1)
                                          << " in the application\n  "
                                          << e << "\nis not an argument of the one occurring in "
                                          << "the equation left-hand-side\n  "
                                          << m_lhs << "\n";);
                            return false;
                        }
                    } else {
                        /* function is not fully applied */
                        trace_primrec_aux(tout() << "primitive recursion on argument #" << (m_arg_idx+1) << " was not used "
                                      << "for '" << m_fn << "' because of the partial application\n  "
                                      << e << "\n";);
                        return false;
                    }
                }
                return true;
            }
            case expr_kind::Let:
                if (!check_rhs(let_value(e))) {
                    return false;
                } else {
                    type_context::tmp_locals locals(m_ctx);
                    return check_rhs(instantiate(let_body(e), locals.push_local_from_let(e)));
                }
            case expr_kind::Lambda:
            case expr_kind::Pi:
                if (!check_rhs(binding_domain(e))) {
                    return false;
                } else {
                    type_context::tmp_locals locals(m_ctx);
                    return check_rhs(instantiate(binding_body(e), locals.push_local_from_binding(e)));
                }
            }
            lean_unreachable();
        }

        bool operator()(expr const & e) {
            return check_rhs(e);
        }
    };

    bool check_rhs(type_context & ctx, expr const & lhs, expr const & fn, expr pattern, unsigned arg_idx, expr const & rhs) {
        pattern = ctx.whnf(pattern);
        return check_rhs_fn(ctx, lhs, fn, pattern, arg_idx)(rhs);
    }

    bool check_eq(type_context & ctx, expr const & eqn, unsigned arg_idx) {
        unpack_eqn ue(ctx, eqn);
        buffer<expr> args;
        expr const & fn  = get_app_args(ue.lhs(), args);
        return check_rhs(ctx, ue.lhs(), fn, args[arg_idx], arg_idx, ue.rhs());
    }

    static bool depends_on_locals(expr const & e, type_context::tmp_locals const & locals) {
        return depends_on_any(e, locals.as_buffer().size(), locals.as_buffer().data());
    }

    /* Return true iff argument arg_idx is a candidate for primitive recursion.
       If the argument type is an indexed family, we store the position of the
       indices (in the function being defined) at m_indices_pos.
       This method also updates m_reflexive (true iff the inductive datatype is reflexive). */
    bool check_arg_type(type_context & ctx, unpack_eqns const & ues, unsigned arg_idx) {
        m_indices_pos.clear();
        type_context::tmp_locals locals(ctx);
        /* We can only use primitive recursion on arg_idx IF
           1- Type parameters do not depend on other arguments of the function being defined. */
        expr fn      = ues.get_fn(0);
        expr fn_type = ctx.infer(fn);
        for (unsigned i = 0; i < arg_idx; i++) {
            fn_type = ctx.whnf(fn_type);
            if (!is_pi(fn_type)) throw_ill_formed_eqns();
            fn_type = instantiate(binding_body(fn_type), locals.push_local_from_binding(fn_type));
        }
        fn_type = ctx.try_to_pi(fn_type);
        if (!is_pi(fn_type)) throw_ill_formed_eqns();
        expr arg_type = ctx.relaxed_whnf(binding_domain(fn_type));
        buffer<expr> I_args;
        expr I        = get_app_args(arg_type, I_args);
        if (!is_constant(I) || !inductive::is_inductive_decl(m_env, const_name(I))) {
            trace_primrec(tout() << "primitive recursion on argument #" << (arg_idx+1) << " was not used "
                          << "for '" << fn << "' because type is not inductive\n  "
                          << arg_type << "\n";);
            return false;
        }
        name I_name   = const_name(I);
        m_reflexive   = is_reflexive_datatype(ctx, I_name);
        unsigned nindices = *inductive::get_num_indices(m_env, I_name);
        if (nindices > 0) {
            lean_assert(I_args.size() >= nindices);
            unsigned first_index_pos = I_args.size() - nindices;
            for (unsigned i = first_index_pos; i < I_args.size(); i++) {
                expr const & idx = I_args[i];
                if (!is_local(idx)) {
                    trace_primrec(tout() << "primitive recursion on argument #" << (arg_idx+1) << " was not used "
                                  << "for '" << fn << "' because the inductive type '" << I << "' is an indexed family, "
                                  << "and index #" << (i+1) << " is not a variable\n  "
                                  << arg_type << "\n";);
                    return false;
                }
                /* Index must be an argument of the function being defined */
                unsigned idx_pos = 0;
                buffer<expr> const & xs = locals.as_buffer();
                for (; idx_pos < xs.size(); idx_pos++) {
                    expr const & x = xs[idx_pos];
                    if (mlocal_name(x) == mlocal_name(idx)) {
                        break;
                    }
                }
                if (idx_pos == xs.size()) {
                    trace_primrec(tout() << "primitive recursion on argument #" << (arg_idx+1) << " was not used "
                                  << "for '" << fn << "' because the inductive type '" << I << "' is an indexed family, "
                                  << "and index #" << (i+1) << " is not an argument of the function being defined\n  "
                                  << arg_type << "\n";);
                    return false;
                }
                /* Index can only depend on other indices in the function being defined. */
                expr idx_type = ctx.infer(idx);
                for (unsigned j = 0; j < idx_pos; j++) {
                    bool j_is_not_index =
                        std::find(m_indices_pos.begin(), m_indices_pos.end(), j) == m_indices_pos.end();
                    if (j_is_not_index && depends_on(idx_type, xs[j])) {
                        trace_primrec(tout() << "primitive recursion on argument #" << (arg_idx+1) << " was not used "
                                      << "for '" << fn << "' because the inductive type '" << I << "' is an indexed family, "
                                      << "and index #" << (i+1) << " depends on argument #" << (j+1) << " of '" << fn << "' "
                                      << "which is not an index of the inductive datatype\n  "
                                      << arg_type << "\n";);
                        return false;
                    }
                }
                m_indices_pos.push_back(idx_pos);
                /* Each index can only occur once */
                for (unsigned j = first_index_pos; j < i; j++) {
                    expr const & prev_idx = I_args[j];
                    if (mlocal_name(prev_idx) == mlocal_name(idx)) {
                        trace_primrec(tout() << "primitive recursion on argument #" << (arg_idx+1) << " was not used "
                                      << "for '" << fn << "' because the inductive type '" << I << "' is an indexed family, "
                                      << "and index #" << (i+1) << " and #" << (j+1) << " must be different variables\n  "
                                      << arg_type << "\n";);
                        return false;
                    }
                }
            }
        }
        for (unsigned i = 0; i < I_args.size() - nindices; i++) {
            if (depends_on_locals(I_args[i], locals)) {
                trace_primrec(tout() << "structural recursion on argument #" << (arg_idx+1) << " was not used "
                              << "for '" << fn << "' because type parameter depends on previous arguments\n  "
                              << arg_type << "\n";);
                return false;
            }
        }
        return true;
    }

    /* Return true iff primitive recursion can be performed on one of the arguments.
       If the result is true, then m_arg_pos will contain the position of the argument,
       and m_indices_pos the position of its indices (when the type of the
       argument is an indexed family). */
    bool find_rec_arg(type_context & ctx, unpack_eqns const & ues) {
        buffer<expr> const & eqns = ues.get_eqns_of(0);
        unsigned arity = ues.get_arity_of(0);
        for (unsigned i = 0; i < arity; i++) {
            if (check_arg_type(ctx, ues, i)) {
                bool ok = true;
                for (expr const & eqn : eqns) {
                    if (!check_eq(ctx, eqn, i)) {
                        ok = false;
                        break;
                    }
                }
                if (ok) {
                    m_arg_pos = i;
                    return true;
                }
            }
        }
        return false;
    }

    optional<expr> operator()(expr const & eqns) {
        m_ref    = eqns;
        m_header = get_equations_header(eqns);

        type_context ctx = mk_type_context();
        unpack_eqns ues(ctx, eqns);
        if (ues.get_num_fns() != 1) {
            trace_primrec(tout() << "primitive recursion is not supported for mutually recursive functions:";
                          for (unsigned i = 0; i < ues.get_num_fns(); i++)
                              tout() << " " << ues.get_fn(i);
                          tout() << "\n";);
            return none_expr();
        }
        if (!find_rec_arg(ctx, ues)) return none_expr();
        expr fn = ues.get_fn(0);
        trace_primrec(tout() << "using primitive recursion on argument #" << (m_arg_pos+1) <<
                      " for '" << fn << "'\n";);


        /* TODO(Leo) */
        return none_expr();
    }
};

optional<expr> try_primitive_rec(environment & env, options const & opts, metavar_context & mctx,
                                  local_context const & lctx, expr const & eqns) {
    primitive_rec_fn F(env, opts, mctx, lctx);
    if (auto r = F(eqns)) {
        env  = F.env();
        mctx = F.mctx();
        return r;
    } else {
        return none_expr();
    }
}

void initialize_primitive_rec() {
    register_trace_class({"eqn_compiler", "primitive_rec"});
    register_trace_class({"debug", "eqn_compiler", "primitive_rec"});
}
void finalize_primitive_rec() {}
}
