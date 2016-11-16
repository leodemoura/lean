/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include "util/serializer.h"
#include "util/optional.h"
#include "kernel/inductive/inductive.h"
#include "library/shared_environment.h"
#include "library/io_state.h"

namespace lean {
class corrupted_file_exception : public exception {
public:
    corrupted_file_exception(std::string const & fname);
};

class module_name {
    optional<unsigned> m_relative;
    name               m_name;
public:
    module_name(name const & n):m_name(n) {}
    module_name(unsigned k, name const & n):m_relative(k), m_name(n) {}
    module_name(optional<unsigned> const & k, name const & n):m_relative(k), m_name(n) {}
    name const & get_name() const { return m_name; }
    bool is_relative() const { return static_cast<bool>(m_relative); }
    optional<unsigned> const & get_k() const { return m_relative; }
};

/** \brief Return the list of declarations performed in the current module */
list<name> const & get_curr_module_decl_names(environment const & env);
/** \brief Return the list of universes declared in the current module */
list<name> const & get_curr_module_univ_names(environment const & env);
/** \brief Return the list of modules directly imported by the current module */
list<module_name> const & get_curr_module_imports(environment const & env);

/** \brief Return an environment based on \c env, where all modules in \c modules are imported.
    Modules included directly or indirectly by them are also imported.
    The environment \c env is usually an empty environment.

    If \c keep_proofs is false, then the proof of the imported theorems is discarded after being
    checked. The idea is to save memory.
*/
environment import_modules(environment const & env, std::string const & base, unsigned num_modules, module_name const * modules,
                           unsigned num_threads, bool keep_proofs, io_state const & ios);
environment import_module(environment const & env, std::string const & base, module_name const & module,
                          unsigned num_threads, bool keep_proofs, io_state const & ios);

/** \brief Return the direct imports of the main module in the given environment. */
list<module_name> get_direct_imports(environment const & env);

/** \brief Return true iff any import in the given environment has been modified in the file system. */
bool imports_have_changed(environment const & env);

/** \brieg Return the list of all imports in the given environment where the olean file is older than the lean file. */
list<module_name> get_out_of_date_imports(environment const & env);

/** \brief Return the .olean file where decl_name was defined. The result is none if the declaration
    was not defined in an imported file. */
optional<std::string> get_decl_olean(environment const & env, name const & decl_name);

/** \brief Return position (line and column number) where the given declaration was defined. */
optional<pos_info> get_decl_pos_info(environment const & env, name const & decl_name);

/** \brief Associate the given position with the given declaration. The information is not saved on
    .olean files. We use this function for attaching position information to temporary functions. */
environment add_transient_decl_pos_info(environment const & env, name const & decl_name, pos_info const & pos);

/** \brief Store/Export module using \c env to the output stream \c out. */
void export_module(std::ostream & out, environment const & env);

/** \brief Export module obtained from \c env as native code to the output stream \c out. */
void export_native_module(std::ostream & out, environment const & env);

/** \brief Store the set of declarations eligble for native compilation in \c decls. */
void decls_to_native_compile(environment const & env, buffer<declaration> & decls);

/** \brief An asynchronous update. It goes into a task queue, and can be executed by a different execution thread. */
typedef std::function<void(shared_environment & env)> asynch_update_fn;

/** \brief Delayed update. It is performed after all imported modules have been loaded.
    The delayes updates are executed based on the import order.
    Example: if module A was imported before B, then delayed updates from A
    are executed before the ones from B.
*/
typedef std::function<environment(environment const & env, io_state const & ios)> delayed_update_fn;

/** \brief A reader for importing data from a stream using deserializer \c d.
    There are three ways to update the environment being constructed.
     1- Direct update it using \c senv.
     2- Asynchronous update using add_asynch_update.
     3- Delayed update using add_delayed_update.
*/
typedef void (*module_object_reader)(deserializer & d, shared_environment & senv,
                                     std::function<void(asynch_update_fn const &)> & add_asynch_update,
                                     std::function<void(delayed_update_fn const &)> & add_delayed_update);

/** \brief Register a module object reader. The key \c k is used to identify the class of objects
    that can be read by the given reader.
*/
void register_module_object_reader(std::string const & k, module_object_reader r);

namespace module {
/** \brief Add a function that should be invoked when the environment is exported.
    The key \c k identifies which module_object_reader should be used to deserialize the object
    when the module is imported.

    \see module_object_reader
*/
environment add(environment const & env, std::string const & k, std::function<void(environment const &, serializer &)> const & writer);

/** \brief Add the global universe declaration to the environment, and mark it to be exported. */
environment add_universe(environment const & env, name const & l);

/** \brief Add the given declaration to the environment, and mark it to be exported. */
environment add(environment const & env, certified_declaration const & d);

/** \brief Return true iff \c n is a definition added to the current module using #module::add */
bool is_definition(environment const & env, name const & n);

/** \brief Add the given inductive declaration to the environment, and mark it to be exported. */
environment add_inductive(environment                       env,
                          inductive::inductive_decl const & decl,
                          bool                              is_trusted);

/** \brief The following function must be invoked to register the quotient type computation rules in the kernel. */
environment declare_quotient(environment const & env);

/** \brief The following function must be invoked to register the builtin HITs in the kernel. */
environment declare_hits(environment const & env);

/* Auxiliary object for setting position information for module declarations.
   It affects module::add and module::add_inductive methods. */
class scope_pos_info {
public:
    scope_pos_info(pos_info const & pos_info);
    ~scope_pos_info();
};
}
void initialize_module();
void finalize_module();
}
