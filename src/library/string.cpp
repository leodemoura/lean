/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <algorithm>
#include "kernel/type_checker.h"
#include "library/kernel_serializer.h"
#include "library/string.h"
#include "library/constants.h"
#include "library/num.h"
#include "library/trace.h"

namespace lean {
static name * g_string_macro         = nullptr;
static std::string * g_string_opcode = nullptr;
static expr * g_nat                  = nullptr;
static expr * g_char                 = nullptr;
static expr * g_char_of_nat          = nullptr;
static expr * g_string               = nullptr;
static expr * g_empty                = nullptr;
static expr * g_str                  = nullptr;
static expr * g_fin_mk               = nullptr;
static expr * g_list_char            = nullptr;
static expr * g_list_cons            = nullptr;
static expr * g_list_nil_char        = nullptr;

expr from_string_core(std::string const & s);

static void display_char_literal_core(std::ostream & out, char c, bool in_string) {
    if (c == '\n')
        out << "\\n";
    else if (c == '\t')
        out << "\\t";
    else if (c == '\r')
        out << "\\r";
    else if (c == 0)
        out << "\\0";
    else if (in_string && c == '\"')
        out << "\\\"";
    else if (!in_string && c == '\'')
        out << "\\'";
    else
        out << c;
}

static void display_char_literal(std::ostream & out, char c) {
    out << "'";
    display_char_literal_core(out, c, false);
    out << "'";
}

static void display_string_literal(std::ostream & out, std::string const & s) {
    out << "\"";
    for (unsigned i = 0; i < s.size(); i++) {
        display_char_literal_core(out, s[i], true);
    }
    out << "\"";
}

format pp_string_literal(std::string const & s) {
    std::ostringstream out;
    display_string_literal(out, s);
    return format(out.str());
}

format pp_char_literal(char c) {
    std::ostringstream out;
    display_char_literal(out, c);
    return format(out.str());
}

/** \brief The string macro is a compact way of encoding strings inside Lean expressions. */
class string_macro : public macro_definition_cell {
    std::string m_value;
public:
    string_macro(std::string const & v):m_value(v) {}
    virtual bool lt(macro_definition_cell const & d) const {
        return m_value < static_cast<string_macro const &>(d).m_value;
    }
    virtual name get_name() const { return *g_string_macro; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const {
        return *g_string;
    }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const {
        return some_expr(from_string_core(m_value));
    }
    virtual unsigned trust_level() const { return 0; }
    virtual bool operator==(macro_definition_cell const & other) const {
        string_macro const * other_ptr = dynamic_cast<string_macro const *>(&other);
        return other_ptr && m_value == other_ptr->m_value;
    }
    virtual void display(std::ostream & out) const {
        display_string_literal(out, m_value);
    }
    virtual format pp(formatter const &) const {
        return pp_string_literal(m_value);
    }
    virtual bool is_atomic_pp(bool, bool) const { return true; }
    virtual unsigned hash() const { return std::hash<std::string>()(m_value); }
    virtual void write(serializer & s) const { s << *g_string_opcode << m_value; }
    std::string const & get_value() const { return m_value; }
};

expr mk_string_macro(std::string const & v) {
    return mk_macro(macro_definition(new string_macro(v)));
}

bool is_string_macro(expr const & e) {
    return is_macro(e) && dynamic_cast<string_macro const *>(macro_def(e).raw()) != nullptr;
}

string_macro const & to_string_macro(expr const & e) {
    lean_assert(is_string_macro(e));
    return *static_cast<string_macro const *>(macro_def(e).raw());
}

void initialize_string() {
    g_string_macro    = new name("string_macro");
    g_string_opcode   = new std::string("Str");
    g_nat             = new expr(Const(get_Nat_name()));
    g_char            = new expr(Const(get_Char_name()));
    g_char_of_nat     = new expr(Const(get_Char_ofNat_name()));
    g_string          = new expr(Const(get_String_name()));
    g_empty           = new expr(Const(get_String_empty_name()));
    g_str             = new expr(Const(get_String_str_name()));
    g_fin_mk          = new expr(Const(get_Fin_mk_name()));
    g_list_char       = new expr(mk_app(mk_constant(get_List_name(), {mk_level_one()}), *g_char));
    g_list_cons       = new expr(mk_constant(get_List_cons_name(), {mk_level_one()}));
    g_list_nil_char   = new expr(mk_app(mk_constant(get_List_nil_name(), {mk_level_one()}), *g_char));
    register_macro_deserializer(*g_string_opcode,
                                [](deserializer & d, unsigned num, expr const *) {
                                    if (num != 0)
                                        throw corrupted_stream_exception();
                                    std::string v = d.read_string();
                                    return mk_string_macro(v);
                                });
}

void finalize_string() {
    delete g_nat;
    delete g_str;
    delete g_empty;
    delete g_string;
    delete g_char_of_nat;
    delete g_char;
    delete g_string_opcode;
    delete g_string_macro;
    delete g_list_char;
    delete g_list_cons;
    delete g_list_nil_char;
    delete g_fin_mk;
}

expr from_string_core(std::string const & s) {
    expr r = *g_empty;
    for (unsigned i = 0; i < s.size(); i++) {
        expr n = to_nat_expr(mpz(static_cast<unsigned char>(s[i])));
        expr c = mk_app(*g_char_of_nat, n);
        r = mk_app(*g_str, c, r);
    }
    return r;
}

expr from_string(std::string const & s) {
    return mk_string_macro(s);
}

optional<char> to_char(expr const & e) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (fn == *g_fin_mk && args.size() == 3) {
        if (auto n = to_num(args[1])) {
            return optional<char>(n->get_unsigned_int());
        } else {
            return optional<char>();
        }
    } else if (fn == *g_char_of_nat && args.size() == 1) {
        if (auto n = to_num(args[0])) {
            return optional<char>(n->get_unsigned_int());
        } else {
            return optional<char>();
        }
    } else {
        return optional<char>();
    }
}

static bool append_char(expr const & e, std::string & r) {
    if (auto c = to_char(e)) {
        r.push_back(*c);
        return true;
    } else {
        return false;
    }
}

bool to_string_core(expr const & e, std::string & r) {
    if (e == *g_empty || e == *g_list_nil_char) {
        return true;
    } else if (is_string_macro(e)) {
        r = to_string_macro(e).get_value();
        return true;
    } else {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        if (fn == *g_str && args.size() == 2) {
            return to_string_core(args[1], r) && append_char(args[0], r);
        } else if (fn == *g_list_cons && args.size() == 3 && args[0] == *g_char) {
            return to_string_core(args[2], r) && append_char(args[1], r);
        } else {
            return false;
        }
    }
}

optional<std::string> to_string(expr const & e) {
    if (is_string_macro(e)) {
        return optional<std::string>(to_string_macro(e).get_value());
    } else {
        std::string tmp;
        if (to_string_core(e, tmp)) {
            return optional<std::string>(tmp);
        } else {
            return optional<std::string>();
        }
    }
}
}
