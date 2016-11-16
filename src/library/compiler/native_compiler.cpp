/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch and Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/vm/vm.h"
#include "library/vm/optimize.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_format.h"
#include "library/util.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/nat_value.h"
#include "library/compiler/preprocess.h"
#include "library/compiler/native_compiler.h"
#include "library/compiler/options.h"
#include "library/compiler/cpp_compiler.h"
#include "library/compiler/vm_compiler.h"
#include "library/compiler/extern.h"
#include "library/module.h"
#include "library/vm/vm.h"
#include "cpp_emitter.h"
#include "used_names.h"
#include "util/lean_path.h"
// #include "util/executable.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

static std::string* g_lean_install_path;

namespace lean {

expr mk_local(name const & n) {
    return ::lean::mk_local(n, mk_neutral_expr());
}

// Helper functions for setting up the install path on boot-up.
// TODO: this is not currently cross platform
void set_install_path(std::string s) {
    // 8 is the size of the string bin/lean which we want to remove from
    // the installed version of Lean.
    auto path = get_exe_location();
    g_lean_install_path = new std::string(path.substr(0, path.size() - 8));
}

std::string get_install_path() {
    return *g_lean_install_path;
}

extern_fn mk_lean_extern(name n, unsigned arity) {
    return extern_fn(true, n, arity);
}

extern_fn mk_extern(name n, unsigned arity) {
    return extern_fn(false, n, arity);
}

class native_compiler_fn {
public:
    environment        m_env;
    cpp_emitter m_emitter;
    native_compiler_mode m_mode;
    name_map<unsigned> m_arity_map;

public:
    native_compiler_fn(environment const & env, native_compiler_mode mode):
        m_env(env), m_emitter(cpp_emitter(std::string("out.cpp"))) {}

    void emit_headers() {
        this->m_emitter.emit_headers();
    }


    // Not the most effcient, need to do two loops.
    void emit_prototypes(buffer<extern_fn> fns) {
        buffer<extern_fn> in_lean_namespace;
        buffer<extern_fn> rest;

        for (auto fn : fns) {
            if (fn.m_in_lean_namespace) {
                in_lean_namespace.push_back(fn);
            } else {
                rest.push_back(fn);
            }
        }

        this->m_emitter.emit_string("namespace lean {\n");

        for (auto fn : in_lean_namespace) {
            auto np = get_vm_builtin_internal_name(fn.m_name);
            std::cout << "Proessing: " << fn.m_name << std::endl;
            if (np && get_vm_builtin_kind(fn.m_name) == vm_builtin_kind::Cases) {
                std::cout << "BUILTIN_CASES: " << fn.m_name << std::endl;
                auto np = get_vm_builtin_internal_name(fn.m_name);
                lean_assert(np);
                this->m_emitter.emit_string("unsigned ");
                this->m_emitter.mangle_name(fn.m_name);
                this->m_emitter.emit_string("(lean::vm_obj const & o, lean::buffer<lean::vm_obj> & data);\n");
            } else {
                this->m_emitter.emit_prototype(fn.m_name, fn.m_arity);
            }

        }
        this->m_emitter.emit_string("}\n\n");
        // We should be really generating things with C linkage to make
        // interfacing with non-cpp stuff possible.
        // this->m_emitter.emit_string("extern \"C\" {\n");
        for (auto fn : rest) {
            if (get_vm_builtin_cases_idx(m_env, fn.m_name)) {
                auto np = get_vm_builtin_internal_name(fn.m_name);
                lean_assert(np);
                this->m_emitter.emit_string("unsigned ");
                this->m_emitter.mangle_name(fn.m_name);
                this->m_emitter.emit_string("(lean::vm_obj const & o, lean::buffer<lean::vm_obj> & data);\n");
            } else {
                this->m_emitter.emit_prototype(fn.m_name, fn.m_arity);
            }
        }
        // this->m_emitter.emit_string("}\n\n");
    }

    void emit_prototype(name const & n, expr e) {
        this->m_emitter.emit_prototype(n, get_arity(e));
    }

    void populate_arity_map(buffer<procedure> const & procs) {
        for (auto & p : procs) {
            m_arity_map.insert(p.m_name, get_arity(p.m_code));
        }
    }

    void populate_arity_map(buffer<extern_fn> const & procs) {
        for (auto & p : procs) {
            m_arity_map.insert(p.m_name, p.m_arity);
        }
    }
};

// Returns the path to the Lean library based on the standard search path,
// and provided options.
std::vector<std::string> native_include_paths() {
    std::vector<std::string> paths;
    auto conf = native::get_config();
    auto native_include_path = std::string(conf.m_native_include_path);

    // std::cout << native_include_path << std::endl;

    // // TODO: support general path parsing here
    if (native_include_path.compare("") == 0)  {
        // Finally look in the default path.
        paths.push_back(get_install_path() + "include/lean_ext");
    } else {
        paths.push_back(native_include_path);
    }

    return paths;
}

std::vector<std::string> native_library_paths() {
    std::vector<std::string> paths;

    auto conf = native::get_config();
    auto native_library_path = std::string(conf.m_native_library_path);

    // // TODO: support general path parsing here
    if (native_library_path.compare("") == 0) {
        // Finally look in the default path.
        paths.push_back(get_install_path() + "lib");
    } else {
        paths.push_back(native_library_path);
    }

    return paths;
}

// Constructs a compiler with the native configuation options applied.
cpp_compiler compiler_with_native_config(native_compiler_mode mode) {
    cpp_compiler gpp;

    if (mode == native_compiler_mode::AOT) {
        gpp = mk_executable_compiler();
    } else {
        gpp = mk_shared_compiler();
    }

    auto conf = native::get_config();

    auto include_paths = native_include_paths();
    auto library_paths = native_library_paths();

    // Setup include paths
    for (auto path : include_paths) {
        gpp.include_path(path);
    }

    for (auto path : library_paths) {
        gpp.library_path(path);
    }

    // Have g++ emit debug information.
    if (conf.m_native_emit_dwarf) {
        gpp.debug(true);
    }

    return gpp;
}

void add_shared_dependencies(cpp_compiler & compiler) {
    compiler.link("gmp")
            .link("pthread")
            .link("mpfr");
}

void native_compile(environment const & env,
                    buffer<extern_fn> & extern_fns,
                    buffer<procedure> & procs,
                    native_compiler_mode mode) {
    native_compiler_fn compiler(env, mode);

    buffer<name> ns;
    compiler.populate_arity_map(procs);
    compiler.populate_arity_map(extern_fns);

    // Emit the header includes.
    compiler.emit_headers();

    // Emit externs (currently only works for builtins).
    compiler.emit_prototypes(extern_fns);

    for (auto & p : procs) {
        compiler.emit_prototype(p.m_name, p.m_code);
    }

    // First we convert for Lean ...
    vm_obj procs_list = mk_vm_simple(0);
    for (auto & p : procs) {
        std::cout << p.m_name << std::endl;
        // std::cout << p.second << std::endl;
        auto tuple = mk_vm_constructor(0, { to_obj(p.m_name), to_obj(p.m_code) });
        procs_list = mk_vm_constructor(1, { tuple, procs_list });
    }

    vm_state S(env, get_global_ios().get_options());
    std::cout << "About to compile" << std::endl;
    auto compiler_name = name({"native", "compile"});
    auto cc = mk_native_closure(env, compiler_name, {});

    std::fstream lean_output("out.lean.cpp", std::ios_base::out);

    vm_obj result = S.invoke(cc, procs_list);
    auto fmt = to_format(result);
    lean_output << "ir:\n";
    lean_output << fmt << std::endl;
    std::string fn = (sstream() << fmt << "\n\n").str();
    compiler.m_emitter.emit_string(fn.c_str());

    // if (mode == native_compiler_mode::AOT) {
    //    compiler.emit_main(procs);
    // }

    // Get a compiler with the config specified by native options, placed
    // in the correct mode.
    auto gpp = compiler_with_native_config(mode);

    // Add all the shared link dependencies.
    add_shared_dependencies(gpp);

    gpp.file("out.cpp")
       .run();
}

void native_preprocess(environment const & env, declaration const & d, buffer<procedure> & procs) {
    lean_trace(name({"compiler", "native"}),
      tout() << "native_preprocess:" << d.get_name() << "\n";);

    // Run the normal preprocessing and optimizations.
    preprocess(env, d, procs);
}

bool is_internal_decl(declaration const & d) {
    auto n = d.get_name();
    return (n == name("_neutral_") ||
            n == name({"native_compiler", "return"}) ||
            is_internal_cnstr(mk_constant(n)) ||
            is_internal_cases(mk_constant(n)) ||
            is_internal_proj(mk_constant(n)));
}

optional<extern_fn> get_builtin(name const & n) {
    auto internal_name = get_vm_builtin_internal_name(n);
    if (internal_name) {
        switch (get_vm_builtin_kind(n)) {
            case vm_builtin_kind::VMFun: {
                return optional<extern_fn>();
            }
            case vm_builtin_kind::CFun: {
                auto arity = get_vm_builtin_arity(n);
                return optional<extern_fn>(
                    mk_lean_extern(internal_name, arity));
            }
            case vm_builtin_kind::Cases: {
                return optional<extern_fn>(
                    mk_lean_extern(internal_name, 2u));
            }
        }
    } else {
        return optional<extern_fn>();
    }
}

void populate_extern_fns(
    environment const & env,
    used_defs const & used,
    buffer<extern_fn> & extern_fns, bool is_library)
{
    used.m_used_names.for_each([&] (name const & n) {
        if (auto builtin = get_builtin(n)) {
             std::cout << "extern fn: " << n << std::endl;
             extern_fns.push_back(mk_lean_extern(n, builtin.value().m_arity));
        } else if (has_extern_attribute(env, n)) {
            extern_fns.push_back(mk_extern(n, 0));
        } else if (is_library) {
            extern_fns.push_back(mk_extern(n, 0));
        }
    });
}

void native_compile_module(environment const & env, buffer<declaration> decls) {
    std::cout << "compiled native module" << std::endl;

    // Preprocess the main function.
    buffer<procedure> all_procs;
    buffer<procedure> main_procs;
    buffer<extern_fn> extern_fns;

    // Compute the live set of names, we attach a callback that will be
    // invoked for every declaration encountered.
    used_defs used_names(env, [&] (declaration const & d) {
        buffer<procedure> procs;
        // The the name is an internal decl we should not add it to the live set.
        if (is_internal_decl(d)) {
            return;
        // We should skip it if its a bulitin, or a builtin_cases on.
        } else if (auto p = get_builtin(d.get_name())) {
            return;
            // extern_fns.push_back(p.value());
        } else if (auto p =  get_vm_builtin_cases_idx(env, d.get_name())) {
            return;
        } else if (has_extern_attribute(env, d.get_name())) {
            lean_unreachable()
        } else {
            native_preprocess(env, d, procs);
            for (auto pair : procs) {
                used_names.names_in_expr(pair.m_code);
                all_procs.push_back(pair);
            }
        }
    });

    // We then loop over the set of procs produced by preprocessing the
    // main function, we transitively collect all names.
    for (auto decl : decls) {
        used_names.names_in_decl(decl);
    }

    // We now need to collect every function we are choosing to
    // declare as external. We emit an extern decl for every
    // function that exists in the Lean namespace, and then
    // an extern decl for every other function, since the
    // symbols must be visible to other shared libraries
    // when loading them.
    populate_extern_fns(env, used_names, extern_fns, true);

    // Finally we assert that there are no more unprocessed declarations.
    lean_assert(used_names.stack_is_empty());

    native_compile(env, extern_fns, all_procs, native_compiler_mode::JIT);
}

void native_compile_binary(environment const & env, declaration const & d) {
    lean_trace(name("native_compile"),
        tout() << "main_fn: " << d.get_name() << "\n";);

    lean_trace(name("native_compiler"),
        tout() << "main_body: " << d.get_value() << "\n";);

    // Preprocess the main function.
    buffer<procedure> all_procs;
    buffer<procedure> main_procs;
    buffer<extern_fn> extern_fns;
    native_preprocess(env, d, main_procs);

    // Compute the live set of names, we attach a callback that will be
    // invoked for every declaration encountered.
    used_defs used_names(env, [&] (declaration const & d) {
        buffer<procedure> procs;
        if (is_internal_decl(d)) {
            return;
        } else if (auto p = get_builtin(d.get_name())) {
            return;
            // extern_fns.push_back(p.value());
        } else if (auto p =  get_vm_builtin_cases_idx(env, d.get_name())) {
            return;
        } else {
            native_preprocess(env, d, procs);
            for (auto pair : procs) {
                used_names.names_in_expr(pair.m_code);
                all_procs.push_back(pair);
            }
        }
    });

    // We then loop over the set of procs produced by preprocessing the
    // main function, we transitively collect all names.
    for (auto pair : main_procs) {
        all_procs.push_back(pair);
        used_names.names_in_preprocessed_body(pair.m_code);
    }

    populate_extern_fns(env, used_names, extern_fns, false);

    // Finally we assert that there are no more unprocessed declarations.
    lean_assert(used_names.stack_is_empty());

    native_compile(env, extern_fns, all_procs, native_compiler_mode::AOT);
}

void native_compile_module(environment const & env) {
    buffer<declaration> decls;
    decls_to_native_compile(env, decls);
    native_compile_module(env, decls);
}

// Setup for the storage of native modules to .olean files.
static std::string *g_native_module_key = nullptr;

static void native_module_reader(
    deserializer & d,
    shared_environment & senv,
    std::function<void(asynch_update_fn const &)> &,
    std::function<void(delayed_update_fn const &)> &)
{
    name fn;
    d >> fn;
    std::cout << "reading native module from meta-data: " << fn << std::endl;
    // senv.update([&](environment const & env) -> environment {
    //     vm_decls ext = get_extension(env);
    //     // ext.update(fn, code_sz, code.data());
    //     // return update(env, ext);
    //     return
    // });
}

environment set_native_module_path(environment & env, name const & n) {
    return module::add(env, *g_native_module_key, [=] (environment const & e, serializer & s) {
        std::cout << "writing out" << n << std::endl;
        s << n;
        native_compile_module(e);
    });
}

void initialize_native_compiler() {
    native::initialize_options();
    register_trace_class({"compiler", "native"});
    register_trace_class({"compiler", "native", "preprocess"});
    g_native_module_key = new std::string("native_module_path");
    register_module_object_reader(*g_native_module_key, native_module_reader);
}

void finalize_native_compiler() {
    native::finalize_options();
    delete g_native_module_key;
}
}
