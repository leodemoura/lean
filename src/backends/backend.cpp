    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <iostream>
#include <memory>
#include <tuple>
#include <utility>
#include "backend.h"
#include "free_vars.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/app_builder.h"
#include "library/extern.h"
#include "library/normalize.h"
#include "library/trace.h"
#include "used_names.h"
#include "util/fresh_name.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

// void print_decl(environment const & env, declaration const & d) {
//     if (d.is_axiom()) {
//         std::cout << "axiom: " << std::endl;
//         std::cout << d.get_name() << std::endl;
//     } else if (d.is_definition()) {
//         std::cout << "def: "
//         << d.get_name()
//         << " : " << d.get_type() << " := "
//         << d.get_value() << std::endl;
//     } else if (d.is_constant_assumption()) {
//         // bool is_definition() const;
//         // bool is_axiom() const;
//         // bool is_theorem() const;
//         // bool is_constant_assumption() const;
//
//         std::cout << "constant assumption: " << std::endl;
//         std::cout << d.get_name() << " : " << d.get_type() << std::endl;
//         bool is_inductive;
//
//         if (inductive::is_intro_rule(env, d.get_name())) {
//             is_inductive = true;
//         } else {
//             is_inductive = false;
//         }
//         std::cout << is_inductive << std::endl;
//
//     } else if (d.is_theorem()) {
//         std::cout << "theorem" << std::endl;
//     }
// }

// Probably should use buffer everywhere. TODO
std::vector<name> to_vector(buffer<name> & names) {
    std::vector<name> rs;
    for (auto n : names) {
        rs.push_back(n);
    }
    return rs;
}

backend::backend(environment const & env, optional<std::string> main_fn)
    : m_env(env), m_tc(m_env) {
    auto main_name = name(main_fn.value());
    auto main = env.get(main_name);
    used_defs used_names(env);
    used_names.names_in_decl(main);
    auto decls_to_compile = std::vector<declaration>();
    used_names.m_used_names.for_each([&] (name const &n) {
        decls_to_compile.push_back(env.get(n));
    });

    for (auto decl : decls_to_compile) {
        this->compile_decl(decl);
    }
}

void backend::compile_decl(declaration const & d) {
    if (d.is_axiom()) {
        std::cout << "axiom: " << std::endl;
        std::cout << d.get_name() << std::endl;
    } else if (d.is_definition()) {
        auto ty = d.get_type();
        auto value = d.get_value();

        std::vector<name> args;
        auto se = this->compile_body(args, value);
        auto p = proc(d.get_name(), args, se);
        this->add_proc(p);
    } else if (d.is_constant_assumption()) {
        if (auto n = inductive::is_intro_rule(this->m_env, d.get_name())) {
            auto tup = inductive::is_inductive_decl(this->m_env, n.value());
            if (tup) {
                auto inductive_types = std::get<2>(tup.value());
                inductive::inductive_decl ind_ty;
                for (auto it : inductive_types) {
                    if (n.value() == inductive::inductive_decl_name(it)) {
                      ind_ty = it;
                    }
                }

                auto intro_rules = inductive::inductive_decl_intros(ind_ty);

                int ctor_index = -1;
                int arity = 0;

                int i = 0;
                for (auto intro : intro_rules) {
                      std::cout << "intro_rule: " << intro << std::endl;
                      std::cout << "kind: " << intro.kind() << std::endl;
                      auto intro_n = inductive::intro_rule_name(intro);
                      auto intro_ty = inductive::intro_rule_type(intro);
                      std::cout << "type: " << intro_ty << std::endl;

                      if (intro_n == d.get_name()) {
                          ctor_index = i;
                          while (is_pi(intro_ty)) {
                              auto arg_ty = binding_domain(intro_ty);
                              if (!is_erasible(arg_ty)) {
                                  arity += 1;
                              }
                              intro_ty = binding_body(intro_ty);
                          }
                          break;
                      }

                      i += 1;
                }

                std::cout << "inductive type " << n.value() << std::endl;
                this->m_ctors.push_back(ctor(ctor_index, d.get_name(), arity));
            } else {
                throw "don't work";
            }
        } else if (this->m_env.is_recursor(d.get_name())) {
            std::cout << "unhandled recursor: " << d.get_name() << std::endl;
        } else {
            std::cout << "unhandled constant assumption: " << d.get_name() << std::endl;
        }
    } else if (d.is_theorem()) {
        std::cout << "theorem" << std::endl;
    } else {
        std::cout << "unhandled case" << d.get_name() << std::endl;
    }
}

shared_ptr<simple_expr> backend::compile_body(std::vector<name> & args, expr const & e) {
    lean_trace(name({"backend", "compile"}),
               tout() << "expr: " << e << "\n";);
    register_trace_class("backend");

    if (is_lambda(e)) {
        buffer<expr> ls;
        auto ex = e;
        while (is_binding(ex)) {
            expr d = instantiate_rev(binding_domain(ex), ls.size(), ls.data());
            auto n = mk_fresh_name(); // (name const & prefix, unsigned k);
            expr l = mk_local(n, binding_name(ex), d, binding_info(ex));
            // If the type is erasible we will remove it from the arguments
            // list.
            if (!is_erasible(binding_domain(ex))) {
                args.push_back(n);
            }
            ls.push_back(l);
            ex = binding_body(ex);
        }
        ex = instantiate_rev(ex, ls.size(), ls.data());
        return this->compile_expr(ex);
    } else {
        return this->compile_expr(e);
    }
}

shared_ptr<simple_expr> backend::compile_expr(expr const & e) {
    std::vector<binding> bindings;
    auto se = compile_expr(e, bindings);
    for (auto binding : bindings) {
        std::cout << binding.first << " : " << binding.second << std::endl;
    }

    return let_binding(bindings, se);
}

shared_ptr<simple_expr> backend::compile_expr(expr const & e, std::vector<binding> & bindings) {
    lean_trace(name({"backend", "compiler_expr"}),
               tout() << "expr: " << e << "\n";);

    switch (e.kind()) {
        case expr_kind::Local:
            return shared_ptr<simple_expr>(new simple_expr_error("local"));
        case expr_kind::Meta:
            std::cout << "meta: not supported" << std::endl;
            break;
        case expr_kind::Var:
            std::cout<< "var: not supported" << std::endl;
            break;
        case expr_kind::Sort:
            std::cout<< "sort: not supported" << std::endl;
            break;
        case expr_kind::Constant:
            return this->compile_expr_const(e);
        case expr_kind::Macro:
            return this->compile_expr_macro(e, bindings);
        case expr_kind::Lambda:
            return this->compile_expr_lambda(e, bindings);
        case expr_kind::Pi:
            std::cout<< "pi: not supported" << std::endl;
            break;
        case expr_kind::App:
            return this->compile_expr_app(e, bindings);
        case expr_kind::Let:
            std::cout << "meta: not supported" << std::endl;
            break;
        case expr_kind::Meta:
            std::cout << "meta: not supported" << std::endl;
            break;
        case expr_kind::Var:
            std::cout<< "var: not supported" << std::endl;
            break;
            std::cout<< "sort: not supported" << std::endl;
            break;
    }
    // Catch-all exeception TODO: make this a real exception w/ error reporting
    throw new std::string("internal error: should of matched an above case");
}

shared_ptr<simple_expr> backend::compile_expr_const(expr const & e) {
    name n = name(const_name(e));
    return shared_ptr<simple_expr>(new simple_expr_var(n));
}

shared_ptr<simple_expr> backend::compile_expr_app(expr const & e, std::vector<binding> & bindings) {
    buffer<expr> args;
    expr const & f = get_app_args(e, args);
    unsigned nargs = args.size();
    std::vector<name> names;

    // First we loop over the arguments, un-rolling each sub-expression into
    // a sequence of bindings, we also store the set of names we will apply
    // the function to.
    for (unsigned i = 0; i < nargs; i++) {
         std::cout << args[i] << std::endl;
         auto ty = m_tc.check_ignore_undefined_universes(args[i]);
         std::cout << "argument type: " << ty.first << std::endl;
         // If the argument is erasible, we should complete the
         // erasure here, by omitting the compiled argument.
         if (!is_erasible(ty.first)) {
             // If the argument is a constant we don't need to generate
             // a fresh binding.
             if (is_constant(args[i])) {
                 names.push_back(const_name(args[i]));
             } else if (is_local(args[i])) {
                 names.push_back(mlocal_name(args[i]));
             } else {
                 auto n = mk_fresh_name();
                 this->bind_name(n, args[i], bindings);
                 names.push_back(n);
             }
        }
    }

    // We now need to handle the function itself, if the applied term is
    // a recursor we will ensure we have emitted a compiled recursor,
    // and then compile a direct call to it.
    //
    // If `f` is just a constant we will directly call it.
    //
    // Finally if `f` is any other kind of expresion we will bind it to
    // a name and then invoke that name.
    if (is_constant(f) && this->m_env.is_recursor(const_name(f))) {
        compile_recursor(f);
        auto callee_name = const_name(f);
        return shared_ptr<simple_expr>(new simple_expr_call(callee_name, names, 1));
    } else if (is_constant(f) &&
               (inductive::is_intro_rule(this->m_env, const_name(f)) ||
               is_extern(this->m_env, const_name(f)))) {
        auto callee_name = const_name(f);
        return shared_ptr<simple_expr>(new simple_expr_call(callee_name, names, 1));
    } else if (is_constant(f)) {
        auto callee_name = const_name(f);
        return shared_ptr<simple_expr>(new simple_expr_call(callee_name, names));
    } else {
        auto callee_name = mk_fresh_name();
        this->bind_name(callee_name, f, bindings);
        return shared_ptr<simple_expr>(new simple_expr_call(callee_name, names));
    }
}

// The current approach to compiling recursors is to transform each one
// into a procedure, and then to erase the cost of each recursor being
// a function call by traditional functional optimizations.
void backend::compile_recursor(expr const & recursor_expr) {
    auto recursor_name = const_name(recursor_expr);

    lean_trace(name({"backend", "compile_recursor"}),
               tout() << "compiling recursor: " << recursor_name << "\n";);

    lean_assert(m_env.is_recursor(recursor_name));

    // The name of the major premise we we are "pattern-matching" on.
    auto scrutinee_name = name("major_premise");

    // We unconditionally call this function, if we have already
    // generated a computational representation of the recursor
    // we just return.
    if (this->m_procs.contains(recursor_name)) {
        return;
    } else {
        auto p = proc();
        p.m_name = recursor_name;
        this->add_proc(p);
    }

    auto inductive_ty_name = inductive::is_elim_rule(m_env, recursor_name).value();
    std::cout << inductive_ty_name << std::endl;

    auto types =
        inductive::is_inductive_decl(this->m_env, inductive_ty_name).value();

    auto inductive_types = std::get<2>(types);
    inductive::inductive_decl inductive_ty;

    for (auto it : inductive_types) {
        if (inductive_ty_name == inductive::inductive_decl_name(it)) {
            inductive_ty = it;
        }
    }

    // Retrieve the elminator's type.
    auto elim_ty = this->m_env.get(recursor_name).get_type();

    // Find where the major premise begins.
    auto major_index = inductive::get_elim_major_idx(this->m_env, recursor_name);

    std::cout << "elim_ty: " << elim_ty << major_index.value() << std::endl;

    buffer<expr> ls;
    int binder_no = 0;

    // Iterate over the type of the elminator instantiating everything with
    // fresh constants of the correct type.
    while (binder_no < major_index.value()) {
        lean_assert(is_pi(elim_ty));
        expr d = instantiate_rev(binding_domain(elim_ty), ls.size(), ls.data());
        expr l = mk_local(mk_fresh_name(), binding_name(elim_ty), d, binding_info(elim_ty));
        ls.push_back(l);
        elim_ty = binding_body(elim_ty);
        binder_no += 1;
    }

    app_builder builder(this->m_env);

    auto elim_prefix = mk_app(recursor_expr, ls.size(), ls.data());
    std::cout << "elim_applied: " << elim_prefix << std::endl;

    auto intro_rules =
        inductive::inductive_decl_intros(inductive_ty);

    buffer<name> intro_names;
    get_intro_rule_names(this->m_env, inductive_ty_name, intro_names);

    // Now we iterate over the introduction rules for the type giving them
    // the same treatment as above, infer the type of the constructor,
    // apply them to constants, forcing the evaluator to only do one
    // level of evaluation, providing us with the correct rhs for our
    // matches.
    std::vector<shared_ptr<simple_expr>> cases;

    for (auto intro_n : intro_names) {
        // std::cout << "kind: " << intro.kind() << std::endl;
        std::cout << "intro_rule: " << intro_n << std::endl;
        auto intro_decl = this->m_env.get(intro_n);
        auto intro_ty = intro_decl.get_type();
        // std::cout << "type: " << intro_ty << std::endl;

        buffer<expr> intro_locals;

        // Iterate over the type of the elminator instantiating everything with
        // fresh constants of the correct type.
        while (is_pi(intro_ty)) {
            expr d = instantiate_rev(binding_domain(intro_ty), intro_locals.size(), intro_locals.data());
            expr l = mk_local(mk_fresh_name(), binding_name(intro_ty), d, binding_info(intro_ty));
            std::cout << "arg" << l << d << std::endl;
            intro_locals.push_back(l);
            intro_ty = binding_body(intro_ty);
        }

        app_builder builder(this->m_env);

        auto applied_intro =
            builder.mk_app(
                intro_n,
                intro_locals.size(),
                intro_locals.data());

        std::vector<binding> bindings;
        int field_index = 0;
        for (auto local : intro_locals) {
            if (is_erasible(mlocal_type(local))) {
                continue;
            }

            auto rhs = shared_ptr<simple_expr>(new
                simple_expr_project(scrutinee_name, field_index));

            auto b = pair<name, shared_ptr<simple_expr>>(
                name(mlocal_name(local)),
                rhs);

            bindings.push_back(b);

            field_index += 1;
        }

        std::cout << "intro_app: " << applied_intro << std::endl;

        auto applied_rec = mk_app(elim_prefix, applied_intro);
        // auto ty = m_tc.check(applied_rec);
        // std::cout << "applied_rec_ty: " << ty.first << std::endl;
        std::cout << "applied_rec: " << applied_rec << std::endl;
        auto normalized = normalize(this->m_tc, applied_rec);
        std::cout << "applied_rec(eval): " << normalized << std::endl;
        auto arm_body = compile_expr(normalized);

        cases.push_back(let_binding(bindings, arm_body));
    }

    std::vector<name> recursor_args;
    for (auto l : ls) {
        if (!is_erasible(mlocal_type(l))) {
            recursor_args.push_back(mlocal_name(l));
        }
    }
    recursor_args.push_back(scrutinee_name);
    auto se = shared_ptr<simple_expr>(new simple_expr_switch(scrutinee_name, cases));
    auto p = proc(recursor_name, recursor_args, se);
    this->add_proc(p);
    std::cout << "done with recursor" << std::endl;
}

shared_ptr<simple_expr> backend::compile_expr_macro(expr const & e, std::vector<binding> & bindings) {
    // Eventually do efficent replacement here.
    //
    // Expand it and then compile the resulting
    // expression.
    auto expanded_expr = m_tc.expand_macro(e);
    if (expanded_expr) {
        return compile_expr(expanded_expr.value(), bindings);
    } else {
        throw "macro expansion failed";
    }
}

shared_ptr<simple_expr> backend::compile_expr_lambda(expr const & e, std::vector<binding> & bindings) {
    // Generate a global name for the closure we are converting.
    name closure_name = this->fresh_name_with_prefix("_$closure$");

    // Peek inside the term and figure out its free variables.
    buffer<name> fvs;
    free_vars(e, fvs);

    for (auto fv : fvs) {
        std::cout << "freevar: " << fv << std::endl;
    }

    // The free variables become arguments for the function pointer we are
    // about to generate, and also must be bound when we allocate a fresh
    // closure.
    auto fv_vector = to_vector(fvs);
    auto args = to_vector(fvs);

    // Finally we compile the body, recursively invoking this procedure
    // if need be.
    auto se = this->compile_body(args, e);

    // We then construct a new top-level procedure corresponding to the closure.
    auto p = proc(closure_name, args, se);
    this->add_proc(p);

    // We then generate a binding for this closure allocation, and return
    // the name of the intermediate expression.
    name binding_name = this->fresh_name();

    auto call_expr = shared_ptr<simple_expr>(
        new simple_expr_closure_alloc(closure_name, fv_vector));

    bindings.push_back(binding(binding_name, call_expr));

    return shared_ptr<simple_expr>(new simple_expr_var(binding_name));
}


shared_ptr<simple_expr> backend::compile_error(std::string msg) {
    return shared_ptr<simple_expr>(new simple_expr_error(msg));
}

void backend::bind_name(name n, expr const & e, std::vector<binding> & bindings) {
    auto simple_arg = this->compile_expr(e, bindings);
    bindings.push_back(binding(n, simple_arg));
}

void backend::add_proc(proc p) {
    this->m_procs.insert(p.m_name, p);
}

name backend::fresh_name() {
    return mk_fresh_name();
}

name backend::fresh_name_with_prefix(name const & prefix) {
    return mk_tagged_fresh_name(prefix);
}

shared_ptr<simple_expr> let_binding(std::vector<binding> bindings, shared_ptr<simple_expr> se) {
    if (bindings.empty()) {
        return se;
    } else {
        return std::shared_ptr<simple_expr>(new simple_expr_let(bindings, se));
    }
}

bool is_erasible(expr const & e) {
    lean_trace(name({"backend", "is_erasible"}),
              tout() << "erase: " << e << "\n";);

    if (is_sort(e)) {
        return true;
    } else if (is_pi(e)) {
        auto co_domain = e;
        while (is_pi(co_domain)) {
            co_domain = binding_body(co_domain);
        }
        return is_sort(co_domain);
    } else {
        return false;
    }
}

}
