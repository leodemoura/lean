    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "c_backend.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "used_names.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

static const char * LEAN_OBJ_TYPE = "lean::obj";

c_backend::c_backend(environment const & env, optional<std::string> main_fn)
    : backend(env, main_fn) {}

// Not really sure if this is suffcient mangling. I can polish this
// over time, first attempt to is to get a linked executable.
void mangle_name(std::ostream& os, name const & n) {
    if (n.is_anonymous()) {
        os << "anon_name?";
    } else if (n.is_string()) {
        auto s = n.to_string("_");
        os << s;
    } else if (n.is_numeral()) {
        auto s = n.to_string("_");
        os << "__lean_nv_" << s;
    } else {
        lean_unreachable();
    }
}

void generate_includes(std::ostream& os) {
    os << "#include \"lean/runtime.h\"" << std::endl << std::endl;
}

void generate_main(std::ostream& os) {
    os << "int main() {" << std::endl;
    os << std::setw(4) << "run_main(___main);" << std::endl;
    os << std::setw(4) << "return 0;" << std::endl;
    os << "}" << std::endl;
}

void c_backend::generate_code(optional<std::string> output_path) {
    std::fstream fs("out.cpp", std::ios_base::out);
    generate_includes(fs);
    for (auto proc : this->m_procs) {
        this->generate_proc(fs, proc);
        fs << std::endl;
    }
    generate_main(fs);
    fs.flush();
    fs.close();
}

void c_backend::generate_proc(std::ostream& os, proc const & p) {
    os << LEAN_OBJ_TYPE << " " << p.m_name << "(";

    auto comma = false;

    for (auto arg : p.m_args) {
        if (comma) {
            os << ", ";
        } else {
            comma = true;
        }
        os << LEAN_OBJ_TYPE << " ";
        mangle_name(os, arg);
    }

    os << ") {" << std::endl;
    os << std::left << std::setw(4);
    os.flush();
    this->generate_simple_expr(os, *p.m_body);
    //os.width(0);

    os << std::endl << "}" << std::endl;
}

void c_backend::generate_simple_expr_var(std::ostream& os, simple_expr const & se) {
    auto n = to_simple_var(&se)->m_name;
    mangle_name(os, n);
}

void c_backend::generate_simple_expr_error(std::ostream& os, simple_expr const & se) {
    auto msg = to_simple_error(&se)->m_error_msg;
    os << "error(\"" << msg.c_str() << "\")";
}

void c_backend::generate_simple_expr_call(std::ostream& os, simple_expr const & se) {
    auto args = to_simple_call(&se)->m_args;
    auto callee = to_simple_call(&se)->m_name;

    mangle_name(os, callee);

    os << "(";
    auto comma = false;

    for (auto name : args) {
        if (comma) {
            os << ", ";
        } else {
            comma = true;
        }
        mangle_name(os, name);
    }

    os << ")";
}

void c_backend::generate_binding(std::ostream& os, pair<name, shared_ptr<simple_expr>> & p) {
    auto n = p.first;
    auto se = p.second;

    os << LEAN_OBJ_TYPE << " ";
    mangle_name(os, n);
    os << " = ";
    this->generate_simple_expr(os, *se);
    os << ";" << std::endl;
}

void c_backend::generate_simple_expr_let(std::ostream& os, simple_expr const & se) {
    auto bindings = to_simple_let(&se)->m_bindings;
    auto body = to_simple_let(&se)->m_body;
    for (auto binding : bindings) {
        this->generate_binding(os, binding);
    }
    this->generate_simple_expr(os, *body);
}

void c_backend::generate_simple_expr(std::ostream& os, simple_expr const & se) {
    switch (se.kind()) {
        case simple_expr_kind::SVar:
            generate_simple_expr_var(os, se);
            break;
        case simple_expr_kind::Call:
            generate_simple_expr_call(os, se);
            break;
        case simple_expr_kind::Let:
            generate_simple_expr_let(os, se);
            break;
        case simple_expr_kind::Error:
            generate_simple_expr_error(os, se);
            break;
    }
}

}
