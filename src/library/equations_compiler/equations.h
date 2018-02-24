/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
#include "library/metavar_context.h"

namespace lean {
class io_state;

bool is_equation(expr const & e);
expr const & equation_lhs(expr const & e);
expr const & equation_rhs(expr const & e);
expr mk_equation(expr const & lhs, expr const & rhs, bool ignore_if_unused = false);
/** \brief Return true if e is of the form <tt>fun a_1 ... a_n, equation</tt> */
bool is_lambda_equation(expr const & e);

/** \brief Return true iff e is an equation created with ignore_if_unused flag set to true.
    \pre is_equation(e) */
bool ignore_equation_if_unused(expr const & e);

/** \brief Placeholder to indicate no equations were provided (e.g., to a match-with expression) */
expr mk_no_equation();
bool is_no_equation(expr const & e);
/** \brief Return true if e is of the form <tt>fun a_1 ... a_n, no_equation</tt> */
bool is_lambda_no_equation(expr const & e);

expr mk_inaccessible(expr const & e);
bool is_inaccessible(expr const & e);

/** \brief Construct the "as pattern" <tt>lhs@rhs</tt> */
expr mk_as_pattern(expr const & lhs, expr const & rhs);
bool is_as_pattern(expr const & e);
expr get_as_pattern_lhs(expr const & e);
expr get_as_pattern_rhs(expr const & e);


struct equations_header {
    unsigned   m_num_fns{0};              /* number of functions being defined */
    list<name> m_fn_names;                /* local names for functions */
    list<name> m_fn_actual_names;         /* Full qualified name and/or private name */
    bool       m_is_private{false};       /* if true, it must be a private definition */
    bool       m_is_lemma{false};         /* if true, equations are defining a lemma */
    bool       m_is_meta{false};          /* the auxiliary declarations should be tagged as meta */
    bool       m_is_noncomputable{false}; /* if true, equation is not computable and code should not be generated */
    bool       m_aux_lemmas{false};       /* if true, we must create equation lemmas and induction principle */
    /* m_prev_errors is true when errors have already being found processing the file,
       and we should minimize error reporting */
    bool       m_prev_errors{false};
    bool       m_gen_code{true};          /* if true, generate byte code for recursive equations */
    equations_header() {}
    equations_header(unsigned num_fns):m_num_fns(num_fns) {}
};

bool operator==(equations_header const & h1, equations_header const & h2);
inline bool operator!=(equations_header const & h1, equations_header const & h2) { return !(h1 == h2); }

expr mk_equations(equations_header const & header, unsigned num_eqs, expr const * eqs, expr const & wf_tacs);
expr mk_equations(equations_header const & header, unsigned num_eqs, expr const * eqs);
expr update_equations(expr const & eqns, buffer<expr> const & new_eqs);
expr update_equations(expr const & eqns, equations_header const & header);
expr remove_wf_annotation_from_equations(expr const & eqns);

bool is_equations(expr const & e);
bool is_wf_equations(expr const & e);
unsigned equations_size(expr const & e);
equations_header const & get_equations_header(expr const & e);
unsigned equations_num_fns(expr const & e);
void to_equations(expr const & e, buffer<expr> & eqns);
expr const & equations_wf_tactics(expr const & e);

/** \brief Return true if \c e is an auxiliary macro used to store the result of mutually recursive declarations.
    For example, if a set of recursive equations is defining \c n mutually recursive functions, we wrap
    the \c n resulting functions (and their types) with an \c equations_result macro. */
bool is_equations_result(expr const & e);
expr mk_equations_result(unsigned n, expr const * rs);
inline expr mk_equations_result(expr const & e) { return mk_equations_result(1, &e); }
unsigned get_equations_result_size(expr const & e);
expr const & get_equations_result(expr const & e, unsigned i);

/* Context for the equation compiler.

   We use this class for two reasons:
   1- Reduce the number of arguments we have to pass around.
   2- Make sure the equation compiler does not depend on the elaborator. */
class equations_context {
protected:
    bool m_has_ownership{true};
    virtual environment & env_core() = 0;
    virtual metavar_context & mctx_core() = 0;
public:
    equations_context() {}
    equations_context(equations_context const &) = delete;
    equations_context(equations_context &&) = delete;
    equations_context const & operator=(equations_context const &) = delete;
    equations_context const & operator=(equations_context &&) = delete;
    virtual ~equations_context() {}

    environment & env() { lean_assert(m_has_ownership); return env_core(); }
    metavar_context & mctx() { lean_assert(m_has_ownership); return mctx_core(); }
    virtual local_context const & lctx() = 0;
    virtual abstract_context_cache & get_cache() = 0;
    virtual options const & get_options() = 0;

    virtual bool try_report(std::exception const & ex) = 0;
    virtual bool try_report(std::exception const & ex, optional<expr> const & ref) = 0;
    virtual void report_or_throw(elaborator_exception const & ex) = 0;

    bool has_ownership() const { return m_has_ownership; }

    /* Create a type_context using `this` cache.
       The type_context takes over the ownership of mctx() and env().
       The ownership can be restored to `this` object using the `restore` method.

       \pre has_ownership() */
    type_context mk_type_context(local_context const & lctx, transparency_mode m = transparency_mode::Semireducible) {
        lean_assert(m_has_ownership);
        m_has_ownership = false;
        return type_context(env_core(), mctx_core(), lctx, get_cache(), m);
    }

    /* See previous method */
    type_context mk_type_context(transparency_mode m = transparency_mode::Semireducible) {
        return mk_type_context(lctx(), m);
    }

    /* Restore ownership of env and mctx to the equations_context.

       \see mk_type_context */
    void restore(type_context const & ctx) {
        lean_assert(!m_has_ownership);
        env_core()  = ctx.env();
        mctx_core() = ctx.mctx();
        m_has_ownership = true;
    }

    /* Similar to `mk_type_context`, but the cache is not used.
       This method is useful for creating `type_context` objects for tracing and reporting error messages.
       It is also useful when we don't need to propagate updates performed to the `metavar_context` back to `this` object. */
    type_context mk_cacheless_type_context(local_context const & lctx, transparency_mode m = transparency_mode::Semireducible) {
        return type_context(env(), get_options(), mctx(), lctx, m);
    }

    type_context mk_cacheless_type_context(transparency_mode m = transparency_mode::Semireducible) {
        return mk_cacheless_type_context(lctx(), m);
    }
};

/* Return true iff \c eqns represents a set of recursive equations.

   \pre ectx.has_ownership() */
bool is_recursive_eqns(equations_context & ectx, expr const & eqns);

void initialize_equations();
void finalize_equations();
}
