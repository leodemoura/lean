/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/standard_kernel.h"
#include "library/hott_kernel.h"
#include "library/module.h"
#include "library/util.h"
#include "library/relation_manager.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_exceptional.h"
#include "library/vm/vm_list.h"

namespace lean {
struct vm_environment : public vm_external {
    environment m_val;
    vm_environment(environment const & v):m_val(v) {}
    virtual void dealloc() override { this->~vm_environment(); get_vm_allocator().deallocate(sizeof(vm_environment), this); }
};

environment const & to_env(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_environment*>(to_external(o)));
    return static_cast<vm_environment*>(to_external(o))->m_val;
}

vm_obj to_obj(environment const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_environment))) vm_environment(n));
}

vm_obj environment_mk_std(vm_obj const & l) {
    return to_obj(mk_environment(force_to_unsigned(l, 0)));
}

vm_obj environment_mk_hott(vm_obj const & l) {
    return to_obj(mk_hott_environment(force_to_unsigned(l, 0)));
}

vm_obj environment_trust_lvl(vm_obj const & env) {
    return mk_vm_nat(to_env(env).trust_lvl());
}

vm_obj environment_is_std(vm_obj const & env) {
    return mk_vm_bool(is_standard(to_env(env)));
}

vm_obj environment_add(vm_obj const & env, vm_obj const & decl) {
    try {
        return mk_vm_exceptional_success(to_obj(module::add(to_env(env), check(to_env(env), to_declaration(decl)))));
    } catch (throwable & ex) {
        return mk_vm_exceptional_exception(ex);
    }
}

vm_obj environment_get(vm_obj const & env, vm_obj const & n) {
    try {
        return mk_vm_exceptional_success(to_obj(to_env(env).get(to_name(n))));
    } catch (throwable & ex) {
        return mk_vm_exceptional_exception(ex);
    }
}

static list<inductive::intro_rule> to_list_intro_rule(vm_obj const & cnstrs) {
    if (is_simple(cnstrs))
        return list<inductive::intro_rule>();
    else
        return list<inductive::intro_rule>(mk_local(to_name(cfield(cfield(cnstrs, 0), 0)),
                                                    to_expr(cfield(cfield(cnstrs, 0), 1))),
                                           to_list_intro_rule(cfield(cnstrs, 1)));
}

vm_obj environment_add_inductive(vm_obj const & env, vm_obj const & n, vm_obj const & ls, vm_obj const & num,
                                 vm_obj const & type, vm_obj const & cnstrs) {
    try {
        environment new_env = module::add_inductive(to_env(env),
                                                    inductive::inductive_decl(to_name(n),
                                                                              to_list_name(ls),
                                                                              force_to_unsigned(num, 0),
                                                                              to_expr(type),
                                                                              to_list_intro_rule(cnstrs)));
        return mk_vm_exceptional_success(to_obj(new_env));
    } catch (throwable & ex) {
        return mk_vm_exceptional_exception(ex);
    }
}

vm_obj environment_is_inductive(vm_obj const & env, vm_obj const & n) {
    return mk_vm_bool(static_cast<bool>(inductive::is_inductive_decl(to_env(env), to_name(n))));
}

vm_obj environment_is_constructor(vm_obj const & env, vm_obj const & n) {
    return mk_vm_bool(static_cast<bool>(inductive::is_intro_rule(to_env(env), to_name(n))));
}

vm_obj environment_inductive_type_of(vm_obj const & env, vm_obj const & n) {
    if (auto I = inductive::is_intro_rule(to_env(env), to_name(n)))
        return mk_vm_some(to_obj(*I));
    else
        return mk_vm_none();
}

vm_obj environment_is_recursor(vm_obj const & env, vm_obj const & n) {
    return mk_vm_bool(static_cast<bool>(inductive::is_elim_rule(to_env(env), to_name(n))));
}

vm_obj environment_is_recursive(vm_obj const & env, vm_obj const & n) {
    return mk_vm_bool(static_cast<bool>(is_recursive_datatype(to_env(env), to_name(n))));
}

vm_obj environment_constructors_of(vm_obj const & env, vm_obj const & n) {
    buffer<name> ns;
    get_intro_rule_names(to_env(env), to_name(n), ns);
    return to_obj(to_list(ns));
}

vm_obj environment_recursor_of(vm_obj const & env, vm_obj const & n) {
    if (auto I = inductive::is_elim_rule(to_env(env), to_name(n)))
        return mk_vm_some(to_obj(*I));
    else
        return mk_vm_none();
}

vm_obj environment_inductive_num_params(vm_obj const & env, vm_obj const & n) {
    if (auto r = inductive::get_num_params(to_env(env), to_name(n)))
        return mk_vm_nat(*r);
    else
        return mk_vm_nat(0);
}

vm_obj environment_inductive_num_indices(vm_obj const & env, vm_obj const & n) {
    if (auto r = inductive::get_num_indices(to_env(env), to_name(n)))
        return mk_vm_nat(*r);
    else
        return mk_vm_nat(0);
}

vm_obj environment_fold(vm_obj const &, vm_obj const & env, vm_obj const & a, vm_obj const & fn) {
    vm_obj r = a;
    to_env(env).for_each_declaration([&](declaration const & d) {
            r = invoke(fn, to_obj(d), r);
        });
    return r;
}

vm_obj environment_relation_info(vm_obj const & env, vm_obj const & n) {
    if (relation_info const * info = get_relation_info(to_env(env), to_name(n))) {
        vm_obj r = mk_vm_pair(mk_vm_pair(mk_vm_nat(info->get_arity()), mk_vm_nat(info->get_lhs_pos())), mk_vm_nat(info->get_rhs_pos()));
        return mk_vm_some(r);
    } else {
        return mk_vm_none();
    }
}

vm_obj environment_refl_for(vm_obj const & env, vm_obj const & n) {
    if (optional<name> const & r = get_refl_info(to_env(env), to_name(n))) {
        return mk_vm_some(to_obj(*r));
    } else {
        return mk_vm_none();
    }
}

vm_obj environment_trans_for(vm_obj const & env, vm_obj const & n) {
    if (optional<name> const & r = get_trans_info(to_env(env), to_name(n))) {
        return mk_vm_some(to_obj(*r));
    } else {
        return mk_vm_none();
    }
}

vm_obj environment_symm_for(vm_obj const & env, vm_obj const & n) {
    if (optional<name> const & r = get_symm_info(to_env(env), to_name(n))) {
        return mk_vm_some(to_obj(*r));
    } else {
        return mk_vm_none();
    }
}

void initialize_vm_environment() {
    DECLARE_VM_BUILTIN(name({"environment", "mk_std"}),                environment_mk_std);
    DECLARE_VM_BUILTIN(name({"environment", "mk_hott"}),               environment_mk_hott);
    DECLARE_VM_BUILTIN(name({"environment", "trust_lvl"}),             environment_trust_lvl);
    DECLARE_VM_BUILTIN(name({"environment", "is_std"}),                environment_is_std);
    DECLARE_VM_BUILTIN(name({"environment", "add"}),                   environment_add);
    DECLARE_VM_BUILTIN(name({"environment", "get"}),                   environment_get);
    DECLARE_VM_BUILTIN(name({"environment", "fold"}),                  environment_fold);
    DECLARE_VM_BUILTIN(name({"environment", "add_inductive"}),         environment_add_inductive);
    DECLARE_VM_BUILTIN(name({"environment", "is_inductive"}),          environment_is_inductive);
    DECLARE_VM_BUILTIN(name({"environment", "is_constructor"}),        environment_is_constructor);
    DECLARE_VM_BUILTIN(name({"environment", "is_recursor"}),           environment_is_recursor);
    DECLARE_VM_BUILTIN(name({"environment", "is_recursive"}),          environment_is_recursive);
    DECLARE_VM_BUILTIN(name({"environment", "inductive_type_of"}),     environment_inductive_type_of);
    DECLARE_VM_BUILTIN(name({"environment", "constructors_of"}),       environment_constructors_of);
    DECLARE_VM_BUILTIN(name({"environment", "recursor_of"}),           environment_recursor_of);
    DECLARE_VM_BUILTIN(name({"environment", "inductive_num_params"}),  environment_inductive_num_params);
    DECLARE_VM_BUILTIN(name({"environment", "inductive_num_indices"}), environment_inductive_num_indices);
    DECLARE_VM_BUILTIN(name({"environment", "relation_info"}),         environment_relation_info);
    DECLARE_VM_BUILTIN(name({"environment", "refl_for"}),              environment_refl_for);
    DECLARE_VM_BUILTIN(name({"environment", "symm_for"}),              environment_symm_for);
    DECLARE_VM_BUILTIN(name({"environment", "trans_for"}),             environment_trans_for);
}

void finalize_vm_environment() {
}
}
