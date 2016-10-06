/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/stackinfo.h"
#include "util/thread.h"
#include "util/init_module.h"
#include "util/numerics/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "kernel/inductive/inductive.h"
#include "kernel/quotient/quotient.h"
#include "library/init_module.h"
#include "library/tactic/init_module.h"
#include "library/constructions/init_module.h"
#include "library/equations_compiler/init_module.h"
#include "library/inductive_compiler/init_module.h"
#include "library/print.h"
#include "library/vm/init_module.h"
#include "library/compiler/init_module.h"
#include "frontends/lean/init_module.h"
#include "frontends/smt2/init_module.h"
#include "backends/init_module.h"
#include "init/init.h"

namespace lean {
void initialize() {
    save_stack_info();
    initialize_util_module();
    initialize_numerics_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_inductive_module();
    initialize_quotient_module();
    init_default_print_fn();
    initialize_library_core_module();
    initialize_vm_core_module();
    initialize_library_module();
    initialize_tactic_module();
    initialize_blast_module();
    initialize_definitional_module();
    initialize_compiler_module();
    initialize_tactic_module();
    initialize_constructions_module();
    initialize_equations_compiler_module();
    initialize_inductive_compiler_module();
    initialize_frontend_lean_module();
    initialize_frontend_smt2_module();
    initialize_backends_module();
    initialize_vm_module();
}
void finalize() {
    run_thread_finalizers();
    finalize_vm_module();
    finalize_frontend_smt2_module();
    finalize_frontend_lean_module();
    finalize_inductive_compiler_module();
    finalize_equations_compiler_module();
    finalize_constructions_module();
    finalize_tactic_module();
    finalize_compiler_module();
    finalize_library_module();
    finalize_vm_core_module();
    finalize_library_core_module();
    finalize_quotient_module();
    finalize_inductive_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_numerics_module();
    finalize_util_module();
    run_post_thread_finalizers();
}

initializer::initializer() {
    initialize();
}

initializer::~initializer() {
    finalize();
    delete_thread_finalizer_manager();
}
}
