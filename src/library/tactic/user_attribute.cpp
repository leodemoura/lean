/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include <string>
#include <limits>
#include "library/attribute_manager.h"
#include "library/constants.h"
#include "library/scoped_ext.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_string.h"
#include "library/tactic/tactic_state.h"
#include "library/cache_helper.h"
#include "library/trace.h"
#include "util/name_hash_map.h"

namespace lean {

/* typed_attribute */
static std::string * g_key = nullptr;

struct user_attr_data : public attr_data {
    // to be filled

    void write(serializer &) const {
        lean_unreachable();
    }
    void read(deserializer &) {
        lean_unreachable();
    }
};

class user_attribute : public typed_attribute<user_attr_data> {
public:
    user_attribute(name const & id, char const * descr) : typed_attribute(id, descr) {}
};


/* Caching */
class user_attr_cache {
private:
    struct entry {
        unsigned m_fingerprint;
        vm_obj   m_val;
        entry(unsigned f, vm_obj const & val):m_fingerprint(f), m_val(val) {}
    };
    name_hash_map<entry> m_cache;

public:
    vm_obj get(environment const & env, attribute const & attr, vm_obj const & cache_handler) {
        auto it = m_cache.find(attr.get_name());
        if (it != m_cache.end()) {
            if (it->second.m_fingerprint == attr.get_fingerprint(env))
                return it->second.m_val;
            lean_trace("user_attributes_cache", tout() << "cached result for [" << attr.get_name() << "] "
                       << "has been found, but cache fingerprint does not match\n";);
        } else {
            lean_trace("user_attributes_cache", tout() << "no cached result for [" << attr.get_name() << "]\n";);
        }

        lean_trace("user_attributes_cache", tout() << "recomputing cache for [" << attr.get_name() << "]\n";);
        buffer<name> instances;
        attr.get_instances(env, instances);
        auto cached = invoke(cache_handler, to_vm_list(to_list(instances), [&](const name & inst) {
            return to_obj(env.get(inst));
        }));
        m_cache.erase(attr.get_name());
        m_cache.insert(mk_pair(attr.get_name(), entry(attr.get_fingerprint(env), cached)));
        return cached;
    }
};

MK_THREAD_LOCAL_GET_DEF(user_attr_cache, get_user_attribute_cache);


/* Persisting */
struct user_attr_ext : public environment_extension {
    name_map<attribute_ptr> m_attrs;
};

struct user_attr_ext_reg {
    unsigned m_ext_id;
    user_attr_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<user_attr_ext>()); }
};

static user_attr_ext_reg * g_ext = nullptr;
static user_attr_ext const & get_extension(environment const & env) {
    return static_cast<user_attr_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, user_attr_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<user_attr_ext>(ext));
}

static environment add_user_attr(environment const & env, name const & d) {
    auto const & ty = env.get(d).get_type();
    if (!is_constant(ty, get_UserAttribute_name()) && !is_constant(ty, get_CachingUserAttribute_name()))
        throw exception("invalid attribute.register argument, must be name of a definition of type user_attribute");

    vm_state vm(env);
    vm_obj const & o = vm.invoke(d, {});
    name const & n = to_name(cfield(o, 0));
    if (is_attribute(env, n))
        throw exception(sstream() << "an attribute named [" << n << "] has already been registered");
    std::string descr = to_string(cfield(o, 1));

    user_attr_ext ext = get_extension(env);
    ext.m_attrs.insert(n, attribute_ptr(new user_attribute(n, descr.c_str())));
    return update(env, ext);
}

static void user_attr_reader(deserializer & d, shared_environment & senv,
                             std::function<void(asynch_update_fn const &)> &,
                             std::function<void(delayed_update_fn const &)> &) {
    name n;
    d >> n;
    senv.update([=](environment const & env) -> environment {
        return add_user_attr(env, n);
    });
}


/* Integration into attribute_manager */
class actual_user_attribute_ext : public user_attribute_ext {
public:
    virtual name_map<attribute_ptr> get_attributes(environment const & env) override {
        return get_extension(env).m_attrs;
    }
};


/* VM builtins */
vm_obj attribute_get_instances(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    buffer<name> b;
    LEAN_TACTIC_TRY;
    get_attribute(s.env(), n).get_instances(s.env(), b);
    LEAN_TACTIC_CATCH(s);
    return mk_tactic_success(to_obj(b), s);
}

vm_obj attribute_register(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    LEAN_TACTIC_TRY;
    auto env = add_user_attr(s.env(), n);
    env = module::add(env, *g_key, [=](environment const &, serializer & s) { s << n; });
    return mk_tactic_success(set_env(s, env));
    LEAN_TACTIC_CATCH(s);
}

vm_obj attribute_fingerprint(vm_obj const & vm_n, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(vm_n);
    unsigned h;
    LEAN_TACTIC_TRY;
    h = get_attribute(s.env(), n).get_fingerprint(s.env());
    LEAN_TACTIC_CATCH(s);
    return mk_tactic_success(mk_vm_nat(h), s);
}

vm_obj caching_user_attribute_get_cache(vm_obj const & vm_attr, vm_obj const & vm_s) {
    auto const & s = to_tactic_state(vm_s);
    auto const & n = to_name(cfield(vm_attr, 0));
    auto const & cache_handler = cfield(vm_attr, 2);
    LEAN_TACTIC_TRY;
    auto cached = get_user_attribute_cache().get(s.env(), get_attribute(s.env(), n), cache_handler);
    return mk_tactic_success(cached, s);
    LEAN_TACTIC_CATCH(s);
}

vm_obj set_basic_attribute_core(vm_obj const & vm_attr_n, vm_obj const & vm_n, vm_obj const & vm_prio, vm_obj const & vm_s) {
    name const & attr_n    = to_name(vm_attr_n);
    name const & n         = to_name(vm_n);
    unsigned prio;
    if (is_none(vm_prio))
        prio = LEAN_DEFAULT_PRIORITY;
    else
        prio = force_to_unsigned(get_some_value(vm_prio), std::numeric_limits<unsigned>::max());
    tactic_state const & s = to_tactic_state(vm_s);
    LEAN_TACTIC_TRY;
    attribute const & attr = get_attribute(s.env(), attr_n);
    if (basic_attribute const * basic_attr = dynamic_cast<basic_attribute const *>(&attr)) {
        bool persistent     = false;
        environment new_env = basic_attr->set(s.env(), get_global_ios(), n, prio, persistent);
        return mk_tactic_success(set_env(s, new_env));
    } else {
        return mk_tactic_exception(sstream() << "set_basic_attribute tactic failed, '" << attr_n << "' is not a basic attribute", s);
    }
    LEAN_TACTIC_CATCH(s);
}

vm_obj unset_attribute(vm_obj const & vm_attr_n, vm_obj const & vm_n, vm_obj const & vm_s) {
    name const & attr_n    = to_name(vm_attr_n);
    name const & n         = to_name(vm_n);
    tactic_state const & s = to_tactic_state(vm_s);
    LEAN_TACTIC_TRY;
    attribute const & attr = get_attribute(s.env(), attr_n);
    bool persistent        = false;
    environment new_env    = attr.unset(s.env(), get_global_ios(), n, persistent);
    return mk_tactic_success(set_env(s, new_env));
    LEAN_TACTIC_CATCH(s);
}


void initialize_user_attribute() {
    DECLARE_VM_BUILTIN(name({"attribute", "get_instances"}),            attribute_get_instances);
    DECLARE_VM_BUILTIN(name({"attribute", "register"}),                 attribute_register);
    DECLARE_VM_BUILTIN(name({"attribute", "fingerprint"}),              attribute_fingerprint);
    DECLARE_VM_BUILTIN(name({"caching_user_attribute", "get_cache"}),   caching_user_attribute_get_cache);
    DECLARE_VM_BUILTIN(name({"tactic",    "set_basic_attribute_core"}), set_basic_attribute_core);
    DECLARE_VM_BUILTIN(name({"tactic",    "unset_attribute"}),          unset_attribute);

    register_trace_class("user_attributes_cache");
    g_ext = new user_attr_ext_reg();
    g_key = new std::string("USR_ATTR");
    register_module_object_reader(*g_key, user_attr_reader);
    set_user_attribute_ext(std::unique_ptr<user_attribute_ext>(new actual_user_attribute_ext));
}
void finalize_user_attribute() {
    delete g_key;
    delete g_ext;
}
}
