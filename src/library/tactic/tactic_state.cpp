/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "library/constants.h"
#include "library/type_context.h"
#include "library/pp_options.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/cache_helper.h"
#include "library/module.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_exceptional.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_option.h"
#include "library/tactic/tactic_state.h"

#ifndef LEAN_DEFAULT_PP_INSTANTIATE_GOAL_MVARS
#define LEAN_DEFAULT_PP_INSTANTIATE_GOAL_MVARS true
#endif

namespace lean {
static name * g_pp_instantiate_goal_mvars = nullptr;

unsigned get_pp_instantiate_goal_mvars(options const & o) {
    return o.get_unsigned(*g_pp_instantiate_goal_mvars, LEAN_DEFAULT_PP_INSTANTIATE_GOAL_MVARS);
}

void tactic_state_cell::dealloc() {
    this->~tactic_state_cell();
    get_vm_allocator().deallocate(sizeof(tactic_state_cell), this);
}

tactic_state::tactic_state(environment const & env, options const & o, metavar_context const & ctx,
                           list<expr> const & gs, expr const & main) {
    m_ptr = new (get_vm_allocator().allocate(sizeof(tactic_state_cell))) tactic_state_cell(env, o, ctx, gs, main);
    m_ptr->inc_ref();
}

optional<expr> tactic_state::get_main_goal() const {
    if (empty(goals())) return none_expr();
    return some_expr(head(goals()));
}

optional<metavar_decl> tactic_state::get_main_goal_decl() const {
    if (empty(goals())) return optional<metavar_decl>();
    return mctx().get_metavar_decl(head(goals()));
}

tactic_state mk_tactic_state_for(environment const & env, options const & o, metavar_context mctx,
                                 local_context const & lctx, expr const & type) {
    expr main = mctx.mk_metavar_decl(lctx, type);
    return tactic_state(env, o, mctx, list<expr>(main), main);
}

tactic_state mk_tactic_state_for(environment const & env, options const & o, local_context const & lctx, expr const & type) {
    metavar_context mctx;
    return mk_tactic_state_for(env, o, mctx, lctx, type);
}

tactic_state set_options(tactic_state const & s, options const & o) {
    return tactic_state(s.env(), o, s.mctx(), s.goals(), s.main());
}

tactic_state set_env(tactic_state const & s, environment const & env) {
    return tactic_state(env, s.get_options(), s.mctx(), s.goals(), s.main());
}

tactic_state set_mctx(tactic_state const & s, metavar_context const & mctx) {
    return tactic_state(s.env(), s.get_options(), mctx, s.goals(), s.main());
}

tactic_state set_env_mctx(tactic_state const & s, environment const & env, metavar_context const & mctx) {
    return tactic_state(env, s.get_options(), mctx, s.goals(), s.main());
}

static list<expr> consume_solved_prefix(metavar_context const & mctx, list<expr> const & gs) {
    if (empty(gs))
        return gs;
    else if (mctx.is_assigned(head(gs)))
        return consume_solved_prefix(mctx, tail(gs));
    else
        return gs;
}

tactic_state set_goals(tactic_state const & s, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), s.mctx(), consume_solved_prefix(s.mctx(), gs), s.main());
}

tactic_state set_mctx_goals(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), mctx, consume_solved_prefix(mctx, gs), s.main());
}

tactic_state set_env_mctx_goals(tactic_state const & s, environment const & env,
                                metavar_context const & mctx, list<expr> const & gs) {
    return tactic_state(env, s.get_options(), mctx, consume_solved_prefix(mctx, gs), s.main());
}

format tactic_state::pp_expr(formatter_factory const & fmtf, expr const & e) const {
    type_context ctx = mk_type_context_for(*this, transparency_mode::All);
    formatter fmt = fmtf(env(), get_options(), ctx);
    return fmt(e);
}

format tactic_state::pp_goal(formatter_factory const & fmtf, expr const & g) const {
    bool inst_mvars            = get_pp_instantiate_goal_mvars(get_options());
    metavar_decl decl          = *mctx().get_metavar_decl(g);
    local_context lctx         = decl.get_context();
    metavar_context mctx_tmp   = mctx();
    type_context ctx(env(), get_options(), mctx_tmp, lctx, transparency_mode::All);
    formatter fmt              = fmtf(env(), get_options(), ctx);
    if (inst_mvars)
        lctx                   = lctx.instantiate_mvars(mctx_tmp);
    format r                   = lctx.pp(fmt);
    unsigned indent            = get_pp_indent(get_options());
    bool unicode               = get_pp_unicode(get_options());
    if (!lctx.empty())
        r += line();
    format turnstile           = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    expr type                  = decl.get_type();
    if (inst_mvars)
        type                   = mctx_tmp.instantiate_mvars(type);
    r += turnstile + space() + nest(indent, fmt(type));
    if (get_pp_goal_compact(get_options()))
        r = group(r);
    return r;
}

format tactic_state::pp(formatter_factory const & fmtf) const {
    format r;
    bool first = true;
    for (auto const & g : goals()) {
        if (first) first = false; else r += line() + line();
        r += pp_goal(fmtf, g);
    }
    if (first) r = format("no goals");
    return r;
}

format tactic_state::pp() const {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return pp(fmtf);
}

format tactic_state::pp_expr(expr const & e) const {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return pp_expr(fmtf, e);
}

format tactic_state::pp_goal(expr const & g) const {
    lean_assert(is_metavar(g));
    lean_assert(mctx().get_metavar_decl(g));
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return pp_goal(fmtf, g);
}

struct vm_tactic_state : public vm_external {
    tactic_state m_val;
    vm_tactic_state(tactic_state const & v):m_val(v) {}
    virtual void dealloc() override {
        this->~vm_tactic_state(); get_vm_allocator().deallocate(sizeof(vm_tactic_state), this);
    }
};

tactic_state const & to_tactic_state(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_tactic_state*>(to_external(o)));
    return static_cast<vm_tactic_state*>(to_external(o))->m_val;
}

vm_obj to_obj(tactic_state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_tactic_state))) vm_tactic_state(s));
}

transparency_mode to_transparency_mode(vm_obj const & o) {
    return static_cast<transparency_mode>(cidx(o));
}

vm_obj to_obj(transparency_mode m) {
    return mk_vm_simple(static_cast<unsigned>(m));
}


vm_obj tactic_state_env(vm_obj const & s) {
    return to_obj(to_tactic_state(s).env());
}

vm_obj tactic_state_to_format(vm_obj const & s) {
    return to_obj(to_tactic_state(s).pp());
}

format pp_expr(tactic_state const & s, expr const & e) {
    return s.pp_expr(e);
}

format pp_indented_expr(tactic_state const & s, expr const & e) {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return nest(get_pp_indent(s.get_options()), line() + s.pp_expr(fmtf, e));
}

vm_obj tactic_state_format_expr(vm_obj const & s, vm_obj const & e) {
    return to_obj(pp_expr(to_tactic_state(s), to_expr(e)));
}

optional<tactic_state> is_tactic_success(vm_obj const & o) {
    if (is_constructor(o) && cidx(o) == 0) {
        return optional<tactic_state>(to_tactic_state(cfield(o, 1)));
    } else {
        return optional<tactic_state>();
    }
}

optional<pair<format, tactic_state>> is_tactic_exception(vm_state & S, options const & opts, vm_obj const & ex) {
    if (is_constructor(ex) && cidx(ex) == 1) {
        vm_obj fmt = S.invoke(cfield(ex, 0), to_obj(opts));
        return optional<pair<format, tactic_state>>(mk_pair(to_format(fmt), to_tactic_state(cfield(ex, 1))));
    } else {
        return optional<pair<format, tactic_state>>();
    }
}

vm_obj mk_tactic_success(vm_obj const & a, tactic_state const & s) {
    return mk_vm_constructor(0, a, to_obj(s));
}

vm_obj mk_tactic_success(tactic_state const & s) {
    return mk_tactic_success(mk_vm_unit(), s);
}

vm_obj mk_tactic_exception(vm_obj const & fn, tactic_state const & s) {
    return mk_vm_constructor(1, fn, to_obj(s));
}

vm_obj mk_tactic_exception(throwable const & ex, tactic_state const & s) {
    vm_obj _ex = to_obj(ex);
    vm_obj fn  = mk_vm_closure(get_throwable_to_format_fun_idx(), 1, &_ex);
    return mk_tactic_exception(fn, s);
}

vm_obj mk_tactic_exception(format const & fmt, tactic_state const & s) {
    vm_state const & S = get_vm_state();
    if (optional<vm_decl> K = S.get_decl(get_Combinator_K_name())) {
        return mk_tactic_exception(mk_vm_closure(K->get_idx(), to_obj(fmt), mk_vm_unit(), mk_vm_unit()), s);
    } else {
        throw exception("failed to create tactic exceptional result, combinator.K is not in the environment, "
                        "this can happen when users are hacking the init folder");
    }
}

vm_obj mk_tactic_exception(char const * msg, tactic_state const & s) {
    return mk_tactic_exception(format(msg), s);
}

vm_obj mk_tactic_exception(sstream const & strm, tactic_state const & s) {
    return mk_tactic_exception(strm.str().c_str(), s);
}

vm_obj mk_tactic_exception(std::function<format()> const & thunk, tactic_state const & s) {
    return mk_tactic_exception(mk_vm_format_thunk(thunk), s);
}

vm_obj mk_no_goals_exception(tactic_state const & s) {
    return mk_tactic_exception("tactic failed, there are no goals to be solved", s);
}

vm_obj tactic_result(vm_obj const & o) {
    tactic_state const & s = to_tactic_state(o);
    metavar_context mctx = s.mctx();
    expr r = mctx.instantiate_mvars(s.main());
    return mk_tactic_success(to_obj(r), set_mctx(s, mctx));
}

vm_obj tactic_format_result(vm_obj const & o) {
    tactic_state const & s = to_tactic_state(o);
    metavar_context mctx = s.mctx();
    expr r = mctx.instantiate_mvars(s.main());
    metavar_decl main_decl = *mctx.get_metavar_decl(s.main());
    type_context ctx(s.env(), s.get_options(), mctx, main_decl.get_context(), transparency_mode::All);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt = fmtf(s.env(), s.get_options(), ctx);
    return mk_tactic_success(to_obj(fmt(r)), s);
}

vm_obj tactic_target(vm_obj const & o) {
    tactic_state const & s = to_tactic_state(o);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    return mk_tactic_success(to_obj(g->get_type()), s);
}

MK_THREAD_LOCAL_GET_DEF(type_context_cache_manager, get_tcm);

type_context mk_type_context_for(environment const & env, options const & o, metavar_context const & mctx,
                                 local_context const & lctx, transparency_mode m) {
    return type_context(env, o, mctx, lctx, get_tcm(), m);
}

type_context mk_type_context_for(tactic_state const & s, local_context const & lctx, transparency_mode m) {
    return mk_type_context_for(s.env(), s.get_options(), s.mctx(), lctx, m);
}

type_context mk_type_context_for(tactic_state const & s, transparency_mode m) {
    local_context lctx;
    if (auto d = s.get_main_goal_decl()) lctx = d->get_context();
    return mk_type_context_for(s, lctx, m);
}

type_context mk_type_context_for(vm_obj const & s) {
    return mk_type_context_for(to_tactic_state(s));
}

type_context mk_type_context_for(vm_obj const & s, vm_obj const & m) {
    return mk_type_context_for(to_tactic_state(s), to_transparency_mode(m));
}

vm_obj tactic_infer_type(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s = to_tactic_state(s0);
    type_context ctx       = mk_type_context_for(s);
    try {
        return mk_tactic_success(to_obj(ctx.infer(to_expr(e))), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_whnf_core(vm_obj const & t, vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s = to_tactic_state(s0);
    type_context ctx       = mk_type_context_for(s, to_transparency_mode(t));
    try {
        return mk_tactic_success(to_obj(ctx.whnf(to_expr(e))), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_eta_expand(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s = to_tactic_state(s0);
    type_context ctx       = mk_type_context_for(s);
    try {
        return mk_tactic_success(to_obj(ctx.eta_expand(to_expr(e))), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_is_class(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s = to_tactic_state(s0);
    type_context ctx       = mk_type_context_for(s);
    try {
        return mk_tactic_success(mk_vm_bool(static_cast<bool>(ctx.is_class(to_expr(e)))), s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_mk_instance(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s = to_tactic_state(s0);
    type_context ctx       = mk_type_context_for(s);
    try {
        if (auto r = ctx.mk_class_instance(to_expr(e))) {
            return mk_tactic_success(to_obj(*r), s);
        } else {
            auto thunk = [=]() {
                format m("tactic.mk_instance failed to generate instance for");
                m += pp_indented_expr(s, to_expr(e));
                return m;
            };
            return mk_tactic_exception(thunk, s);
        }
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_unify_core(vm_obj const & t, vm_obj const & e1, vm_obj const & e2, vm_obj const & s0) {
    tactic_state const & s = to_tactic_state(s0);
    type_context ctx       = mk_type_context_for(s, to_transparency_mode(t));
    try {
        bool r = ctx.is_def_eq(to_expr(e1), to_expr(e2));
        if (r)
            return mk_tactic_success(set_mctx(s, ctx.mctx()));
        else
            return mk_tactic_exception("unify tactic failed", s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_is_def_eq_core(vm_obj const & t, vm_obj const & e1, vm_obj const & e2, vm_obj const & s0) {
    tactic_state const & s = to_tactic_state(s0);
    type_context ctx       = mk_type_context_for(s, to_transparency_mode(t));
    type_context::tmp_mode_scope scope(ctx);
    try {
        bool r = ctx.is_def_eq(to_expr(e1), to_expr(e2));
        if (r)
            return mk_tactic_success(s);
        else
            return mk_tactic_exception("is_def_eq failed", s);
    } catch (exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_get_local(vm_obj const & n, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx       = g->get_context();
    optional<local_decl> d   = lctx.get_local_decl_from_user_name(to_name(n));
    if (!d) return mk_tactic_exception(sstream() << "get_local tactic failed, unknown '" << to_name(n) << "' local", s);
    return mk_tactic_success(to_obj(d->mk_ref()), s);
}

vm_obj tactic_local_context(vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx       = g->get_context();
    buffer<expr> r;
    lctx.for_each([&](local_decl const & d) { r.push_back(d.mk_ref()); });
    return mk_tactic_success(to_obj(to_list(r)), s);
}

vm_obj tactic_get_unused_name(vm_obj const & n, vm_obj const & vm_i, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    name unused_name;
    if (is_none(vm_i)) {
        unused_name = g->get_context().get_unused_name(to_name(n));
    } else {
        unsigned i  = force_to_unsigned(get_some_value(vm_i), 0);
        unused_name = g->get_context().get_unused_name(to_name(n), i);
    }
    return mk_tactic_success(to_obj(unused_name), s);
}

vm_obj rotate_left(unsigned n, tactic_state const & s) {
    buffer<expr> gs;
    to_buffer(s.goals(), gs);
    unsigned sz = gs.size();
    if (sz == 0)
        return mk_tactic_success(s);
    n = n%sz;
    std::rotate(gs.begin(), gs.begin() + n, gs.end());
    return mk_tactic_success(set_goals(s, to_list(gs)));
}

vm_obj tactic_rotate_left(vm_obj const & n, vm_obj const & s) {
    return rotate_left(force_to_unsigned(n, 0), to_tactic_state(s));
}

vm_obj tactic_get_goals(vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    return mk_tactic_success(to_obj(s.goals()), s);
}

vm_obj set_goals(list<expr> const & gs, tactic_state const & s) {
    buffer<expr> new_gs;
    metavar_context const & mctx = s.mctx();
    for (expr const & g : gs) {
        if (!mctx.get_metavar_decl(g)) {
            return mk_tactic_exception("invalid set_goals tactic, expressions must be meta-variables "
                                       "that have been declared in the current tactic_state", s);
        }
        if (!mctx.is_assigned(g))
            new_gs.push_back(g);
    }
    return mk_tactic_success(set_goals(s, to_list(new_gs)));
}

vm_obj tactic_set_goals(vm_obj const & gs, vm_obj const & s) {
    return set_goals(to_list_expr(gs), to_tactic_state(s));
}

vm_obj tactic_mk_meta_univ(vm_obj const & s) {
    metavar_context mctx = to_tactic_state(s).mctx();
    level u = mctx.mk_univ_metavar_decl();
    return mk_tactic_success(to_obj(u), set_mctx(to_tactic_state(s), mctx));
}

vm_obj tactic_mk_meta_var(vm_obj const & t, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    metavar_context mctx     = s.mctx();
    local_context lctx;
    if (optional<metavar_decl> g = s.get_main_goal_decl()) {
        lctx = g->get_context();
    }
    expr m = mctx.mk_metavar_decl(lctx, to_expr(t));
    return mk_tactic_success(to_obj(m), set_mctx(s, mctx));
}

vm_obj tactic_get_univ_assignment(vm_obj const & u, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    metavar_context mctx     = s.mctx();
    if (!is_meta(to_level(u))) {
        return mk_tactic_exception("get_univ_assignment tactic failed, argument is not an universe metavariable", s);
    } else if (auto r = mctx.get_assignment(to_level(u))) {
        return mk_tactic_success(to_obj(*r), s);
    } else {
        return mk_tactic_exception("get_univ_assignment tactic failed, universe metavariable is not assigned", s);
    }
}

vm_obj tactic_get_assignment(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s   = to_tactic_state(s0);
    metavar_context mctx     = s.mctx();
    if (!is_metavar(to_expr(e))) {
        return mk_tactic_exception("get_assignment tactic failed, argument is not an universe metavariable", s);
    } else if (auto r = mctx.get_assignment(to_expr(e))) {
        return mk_tactic_success(to_obj(*r), s);
    } else {
        return mk_tactic_exception("get_assignment tactic failed, metavariable is not assigned", s);
    }
}

vm_obj tactic_state_get_options(vm_obj const & s) {
    return to_obj(to_tactic_state(s).get_options());
}

vm_obj tactic_state_set_options(vm_obj const & s, vm_obj const & o) {
    return to_obj(set_options(to_tactic_state(s), to_options(o)));
}

vm_obj tactic_mk_fresh_name(vm_obj const & s) {
    return mk_tactic_success(to_obj(mk_fresh_name()), to_tactic_state(s));
}

vm_obj tactic_is_trace_enabled_for(vm_obj const & n) {
    return mk_vm_bool(is_trace_class_enabled(to_name(n)));
}

vm_obj tactic_instantiate_mvars(vm_obj const & e, vm_obj const & _s) {
    tactic_state const & s = to_tactic_state(_s);
    metavar_context mctx = s.mctx();
    expr r = mctx.instantiate_mvars(to_expr(e));
    return mk_tactic_success(to_obj(r), set_mctx(s, mctx));
}

vm_obj tactic_add_decl(vm_obj const & d, vm_obj const & _s) {
    tactic_state const & s  = to_tactic_state(_s);
    try {
        environment new_env = module::add(s.env(), check(s.env(), to_declaration(d)));
        return mk_tactic_success(set_env(s, new_env));
    } catch (throwable & ex) {
        return mk_tactic_exception(ex, s);
    }
}

void initialize_tactic_state() {
    DECLARE_VM_BUILTIN(name({"tactic_state", "env"}),            tactic_state_env);
    DECLARE_VM_BUILTIN(name({"tactic_state", "format_expr"}),    tactic_state_format_expr);
    DECLARE_VM_BUILTIN(name({"tactic_state", "to_format"}),      tactic_state_to_format);
    DECLARE_VM_BUILTIN(name({"tactic_state", "get_options"}),    tactic_state_get_options);
    DECLARE_VM_BUILTIN(name({"tactic_state", "set_options"}),    tactic_state_set_options);
    DECLARE_VM_BUILTIN(name({"tactic", "target"}),               tactic_target);
    DECLARE_VM_BUILTIN(name({"tactic", "result"}),               tactic_result);
    DECLARE_VM_BUILTIN(name({"tactic", "format_result"}),        tactic_format_result);
    DECLARE_VM_BUILTIN(name({"tactic", "infer_type"}),           tactic_infer_type);
    DECLARE_VM_BUILTIN(name({"tactic", "whnf_core"}),            tactic_whnf_core);
    DECLARE_VM_BUILTIN(name({"tactic", "is_def_eq_core"}),       tactic_is_def_eq_core);
    DECLARE_VM_BUILTIN(name({"tactic", "eta_expand"}),           tactic_eta_expand);
    DECLARE_VM_BUILTIN(name({"tactic", "is_class"}),             tactic_is_class);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_instance"}),          tactic_mk_instance);
    DECLARE_VM_BUILTIN(name({"tactic", "unify_core"}),           tactic_unify_core);
    DECLARE_VM_BUILTIN(name({"tactic", "get_local"}),            tactic_get_local);
    DECLARE_VM_BUILTIN(name({"tactic", "local_context"}),        tactic_local_context);
    DECLARE_VM_BUILTIN(name({"tactic", "get_unused_name"}),      tactic_get_unused_name);
    DECLARE_VM_BUILTIN(name({"tactic", "rotate_left"}),          tactic_rotate_left);
    DECLARE_VM_BUILTIN(name({"tactic", "get_goals"}),            tactic_get_goals);
    DECLARE_VM_BUILTIN(name({"tactic", "set_goals"}),            tactic_set_goals);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_meta_univ"}),         tactic_mk_meta_univ);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_meta_var"}),          tactic_mk_meta_var);
    DECLARE_VM_BUILTIN(name({"tactic", "get_univ_assignment"}),  tactic_get_univ_assignment);
    DECLARE_VM_BUILTIN(name({"tactic", "get_assignment"}),       tactic_get_assignment);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_fresh_name"}),        tactic_mk_fresh_name);
    DECLARE_VM_BUILTIN(name({"tactic", "is_trace_enabled_for"}), tactic_is_trace_enabled_for);
    DECLARE_VM_BUILTIN(name({"tactic", "instantiate_mvars"}),    tactic_instantiate_mvars);
    DECLARE_VM_BUILTIN(name({"tactic", "add_decl"}),             tactic_add_decl);
    g_pp_instantiate_goal_mvars = new name{"pp", "instantiate_goal_mvars"};
    register_bool_option(*g_pp_instantiate_goal_mvars, LEAN_DEFAULT_PP_INSTANTIATE_GOAL_MVARS,
                         "(pretty printer) instantiate assigned metavariables before pretty printing goals");
}

void finalize_tactic_state() {
    delete g_pp_instantiate_goal_mvars;
}
}
