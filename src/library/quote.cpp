/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "library/placeholder.h"
#include "library/constants.h"
#include "library/annotation.h"
#include "library/kernel_serializer.h"

namespace lean {
static std::string * g_quote_opcode = nullptr;
static expr * g_pexpr               = nullptr;
static name * g_quote_macro         = nullptr;

/** \brief The quoted expression macro is a compact way of encoding quoted expressions inside Lean expressions. */
class quote_macro : public macro_definition_cell {
    expr m_value;
public:
    quote_macro(expr const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const {
        return m_value < static_cast<quote_macro const &>(d).m_value;
    }
    virtual name get_name() const { return *g_quote_macro; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const {
        return *g_pexpr;
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const {
        return optional<expr>();
    }
    virtual unsigned trust_level() const { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const {
        quote_macro const * other_ptr = dynamic_cast<quote_macro const *>(&other);
        return other_ptr && m_value == other_ptr->m_value;
    }
    virtual void display(std::ostream & out) const {
        out << "`(" << m_value << ")";
    }
    virtual format pp(formatter const & fmt) const {
        return format("`(") + nest(2, fmt(m_value)) + format(")");
    }
    virtual bool is_atomic_pp(bool, bool) const { return false; }
    virtual unsigned hash() const { return m_value.hash(); }
    virtual void write(serializer & s) const { s << *g_quote_opcode << m_value; }
    expr const & get_value() const { return m_value; }
};

expr mk_quote_core(expr const & e) {
    return mk_macro(macro_definition(new quote_macro(e)));
}

bool is_quote(expr const & e) {
    return is_macro(e) && dynamic_cast<quote_macro const *>(macro_def(e).raw()) != nullptr;
}

expr const & get_quote_expr(expr const & e) {
    lean_assert(is_quote(e));
    return static_cast<quote_macro const *>(macro_def(e).raw())->get_value();
}

static name * g_antiquote = nullptr;

expr mk_antiquote(expr const & e) { return mk_annotation(*g_antiquote, e); }
bool is_antiquote(expr const & e) { return is_annotation(e, *g_antiquote); }
expr const & get_antiquote_expr(expr const & e) {
    lean_assert(is_antiquote(e));
    return get_annotation_arg(e);
}

expr mk_quote(expr const & e) {
    name x("_x");
    buffer<expr> locals;
    buffer<expr> aqs;
    expr s = replace(e, [&](expr const & t, unsigned) {
            if (is_antiquote(t)) {
                expr local = mk_local(mk_fresh_name(), x.append_after(locals.size() + 1),
                                      mk_expr_placeholder(), binder_info());
                locals.push_back(local);
                aqs.push_back(get_antiquote_expr(t));
                return some_expr(local);
            }
            return none_expr();
        });
    expr r        = mk_quote_core(Fun(locals, s));
    expr subst    = mk_constant(get_PExpr_subst_name());
    expr to_pexpr = mk_constant(get_toPExpr_name());
    for (expr const & aq : aqs) {
        r = mk_app(subst, r, mk_app(to_pexpr, aq));
    }
    return r;
}

void initialize_quote() {
    g_quote_macro    = new name("quote_macro");
    g_quote_opcode   = new std::string("Quote");
    g_pexpr          = new expr(Const(get_PExpr_name()));

    g_antiquote  = new name("antiquote");
    register_annotation(*g_antiquote);

    register_macro_deserializer(*g_quote_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    expr e;
                                    d >> e;
                                    return mk_quote_core(e);
                                });
}

void finalize_quote() {
    delete g_quote_macro;
    delete g_quote_opcode;
    delete g_pexpr;
    delete g_antiquote;
}
}
