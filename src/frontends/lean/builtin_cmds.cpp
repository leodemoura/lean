/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/timeit.h"
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "library/scoped_ext.h"
#include "library/trace.h"
#include "library/aliases.h"
#include "library/export_decl.h"
#include "library/protected.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/class.h"
#include "library/flycheck.h"
#include "library/user_recursors.h"
#include "library/pp_options.h"
#include "library/attribute_manager.h"
#include "library/aux_recursors.h"
#include "library/private.h"
#include "library/type_context.h"
#include "library/reducible.h"
#include "library/typed_expr.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/kabstract.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/simplifier/simp_extensions.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/print_cmd.h"
// #include "frontends/lean/begin_end_annotation.h"
#include "frontends/lean/decl_cmds.h"
// #include "frontends/lean/tactic_hint.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/decl_attributes.h"

namespace lean {
environment section_cmd(parser & p) {
    name n;
    if (p.curr_is_identifier())
        n = p.check_atomic_id_next("invalid section, atomic identifier expected");
    p.push_local_scope();
    return push_scope(p.env(), p.ios(), scope_kind::Section, n);
}

// Execute open command
environment execute_open(environment env, io_state const & ios, export_decl const & edecl);

environment replay_export_decls_core(environment env, io_state const & ios, unsigned old_sz) {
    list<export_decl> new_export_decls = get_active_export_decls(env);
    unsigned new_sz = length(new_export_decls);
    lean_assert(new_sz >= old_sz);
    unsigned i = 0;
    for (export_decl const & d : new_export_decls) {
        if (i >= new_sz - old_sz)
            break;
        env = execute_open(env, ios, d);
        i++;
    }
    return env;
}

environment replay_export_decls_core(environment env, io_state const & ios) {
    return replay_export_decls_core(env, ios, 0);
}

environment execute_open(environment env, io_state const & ios, export_decl const & edecl) {
    unsigned fingerprint = 0;
    name const & ns = edecl.m_ns;
    fingerprint = hash(fingerprint, ns.hash());
    unsigned old_export_decls_sz = length(get_active_export_decls(env));
    env = activate_export_decls(env, ns);
    for (auto const & p : edecl.m_renames) {
        fingerprint = hash(hash(fingerprint, p.first.hash()), p.second.hash());
        env = add_expr_alias(env, p.first, p.second);
    }
    for (auto const & n : edecl.m_except_names) {
        fingerprint = hash(fingerprint, n.hash());
    }
    if (!edecl.m_had_explicit) {
        buffer<name> except_names;
        to_buffer(edecl.m_except_names, except_names);
        env = add_aliases(env, ns, edecl.m_as, except_names.size(), except_names.data());
    }
    env = update_fingerprint(env, fingerprint);
    return replay_export_decls_core(env, ios, old_export_decls_sz);
}

environment namespace_cmd(parser & p) {
    name n = p.check_decl_id_next("invalid namespace declaration, identifier expected");
    p.push_local_scope();
    unsigned old_export_decls_sz = length(get_active_export_decls(p.env()));
    environment env = push_scope(p.env(), p.ios(), scope_kind::Namespace, n);
    env = activate_export_decls(env, get_namespace(env));
    return replay_export_decls_core(env, p.ios(), old_export_decls_sz);
}

static environment redeclare_aliases(environment env, parser & p,
                                     local_level_decls old_level_decls,
                                     list<pair<name, expr>> old_entries) {
    environment const & old_env = p.env();
    if (!in_section(old_env))
        return env;
    list<pair<name, expr>> new_entries = p.get_local_entries();
    buffer<pair<name, expr>> to_redeclare;
    unsigned new_len = length(new_entries);
    unsigned old_len = length(old_entries);
    lean_assert(old_len >= new_len);
    name_set popped_locals;
    while (old_len > new_len) {
        pair<name, expr> entry = head(old_entries);
        if (is_local_ref(entry.second))
            to_redeclare.push_back(entry);
        else if (is_local(entry.second))
            popped_locals.insert(mlocal_name(entry.second));
        old_entries = tail(old_entries);
        old_len--;
    }
    name_set popped_levels;
    local_level_decls level_decls = p.get_local_level_decls();
    old_level_decls.for_each([&](name const & n, level const & l) {
            if (is_param(l) && !level_decls.contains(n))
                popped_levels.insert(param_id(l));
        });
    for (auto const & entry : to_redeclare) {
        expr new_ref = update_local_ref(entry.second, popped_levels, popped_locals);
        if (!is_constant(new_ref))
            env = p.add_local_ref(env, entry.first, new_ref);
    }
    return env;
}

environment end_scoped_cmd(parser & p) {
    local_level_decls level_decls  = p.get_local_level_decls();
    list<pair<name, expr>> entries = p.get_local_entries();
    p.pop_local_scope();
    if (p.curr_is_identifier()) {
        name n = p.check_id_next("invalid end of scope, identifier expected");
        environment env = pop_scope(p.env(), p.ios(), n);
        return redeclare_aliases(env, p, level_decls, entries);
    } else {
        environment env = pop_scope(p.env(), p.ios());
        return redeclare_aliases(env, p, level_decls, entries);
    }
}

environment check_cmd(parser & p) {
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    type_checker tc(p.env(), true, false);
    expr type = tc.check(e, ls);
    auto out              = regular(p.env(), p.ios(), tc);
    formatter fmt         = out.get_formatter();
    unsigned indent       = get_pp_indent(p.get_options());
    format e_fmt    = fmt(e);
    format type_fmt = fmt(type);
    format r = group(e_fmt + space() + colon() + nest(indent, line() + type_fmt));
    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        out << "check result:\n";
    }
    out << mk_pair(r, p.get_options()) << endl;
    return p.env();
}

environment eval_cmd(parser & p) {
    bool whnf   = false;
    if (p.curr_is_token(get_whnf_tk())) {
        p.next();
        whnf = true;
    }
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    expr r;
    if (whnf) {
        type_checker tc(p.env(), true, false);
        r = tc.whnf(e);
    } else {
        type_checker tc(p.env(), true, false);
        bool eta = false;
        r = normalize(tc, e, eta);
    }
    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.ios().get_regular_stream() << "eval result:\n";
    }
    type_context tc(p.env(), p.get_options());
    auto out = regular(p.env(), p.ios(), tc);
    out << r << endl;
    return p.env();
}

environment exit_cmd(parser & p) {
    flycheck_warning wrn(p.ios());
    p.display_warning_pos(p.cmd_pos());
    p.ios().get_regular_stream() << " using 'exit' to interrupt Lean" << std::endl;
    throw interrupt_parser();
}

environment set_option_cmd(parser & p) {
    auto id_kind = parse_option_name(p, "invalid set option, identifier (i.e., option name) expected");
    name id       = id_kind.first;
    option_kind k = id_kind.second;
    if (k == BoolOption) {
        if (p.curr_is_token_or_id(get_true_tk()))
            p.set_option(id, true);
        else if (p.curr_is_token_or_id(get_false_tk()))
            p.set_option(id, false);
        else
            throw parser_error("invalid Boolean option value, 'true' or 'false' expected", p.pos());
        p.next();
    } else if (k == StringOption) {
        if (!p.curr_is_string())
            throw parser_error("invalid option value, given option is not a string", p.pos());
        p.set_option(id, p.get_str_val());
        p.next();
    } else if (k == DoubleOption) {
        p.set_option(id, p.parse_double());
    } else if (k == UnsignedOption || k == IntOption) {
        p.set_option(id, p.parse_small_nat());
    } else {
        throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", p.pos());
    }
    p.updt_options();
    environment env = p.env();
    return update_fingerprint(env, p.get_options().hash());
}

static void check_identifier(parser & p, environment const & env, name const & ns, name const & id) {
    name full_id = ns + id;
    if (!env.find(full_id))
        throw parser_error(sstream() << "invalid 'open' command, unknown declaration '" << full_id << "'", p.pos());
}

// open/export id (as id)? (id ...) (renaming id->id id->id) (hiding id ... id)
environment open_export_cmd(parser & p, bool open) {
    environment env = p.env();
    while (true) {
        auto pos   = p.pos();
        name ns    = p.check_id_next("invalid 'open/export' command, identifier expected");
        optional<name> real_ns = to_valid_namespace_name(env, ns);
        if (!real_ns)
            throw parser_error(sstream() << "invalid namespace name '" << ns << "'", pos);
        ns = *real_ns;
        name as;
        if (p.curr_is_token_or_id(get_as_tk())) {
            p.next();
            as = p.check_id_next("invalid 'open/export' command, identifier expected");
        }
        buffer<name> exception_names;
        buffer<pair<name, name>> renames;
        bool found_explicit = false;
        // Remark: we currently to not allow renaming and hiding of universe levels
        env = mark_namespace_as_open(env, ns);
        while (p.curr_is_token(get_lparen_tk())) {
            p.next();
            if (p.curr_is_token_or_id(get_renaming_tk())) {
                p.next();
                while (p.curr_is_identifier()) {
                    name from_id = p.get_name_val();
                    p.next();
                    p.check_token_next(get_arrow_tk(), "invalid 'open/export' command renaming, '->' expected");
                    name to_id = p.check_id_next("invalid 'open/export' command renaming, identifier expected");
                    check_identifier(p, env, ns, from_id);
                    exception_names.push_back(from_id);
                    renames.emplace_back(as+to_id, ns+from_id);
                }
            } else if (p.curr_is_token_or_id(get_hiding_tk())) {
                p.next();
                while (p.curr_is_identifier()) {
                    name id = p.get_name_val();
                    p.next();
                    check_identifier(p, env, ns, id);
                    exception_names.push_back(id);
                }
            } else if (p.curr_is_identifier()) {
                found_explicit = true;
                while (p.curr_is_identifier()) {
                    name id = p.get_name_val();
                    p.next();
                    check_identifier(p, env, ns, id);
                    renames.emplace_back(as+id, ns+id);
                }
            } else {
                throw parser_error("invalid 'open/export' command option, "
                                   "identifier, 'hiding' or 'renaming' expected", p.pos());
            }
            if (found_explicit && !exception_names.empty())
                throw parser_error("invalid 'open/export' command option, "
                                   "mixing explicit and implicit 'open/export' options", p.pos());
            p.check_token_next(get_rparen_tk(), "invalid 'open/export' command option, ')' expected");
        }
        export_decl edecl(ns, as, found_explicit, renames, exception_names);
        env = execute_open(env, p.ios(), edecl);
        if (!open) {
            env = add_export_decl(env, edecl);
        }
        if (!p.curr_is_identifier())
            break;
    }
    return env;
}
static environment open_cmd(parser & p) { return open_export_cmd(p, true); }
static environment export_cmd(parser & p) { return open_export_cmd(p, false); }

static environment erase_cache_cmd(parser & p) {
    name n = p.check_id_next("invalid #erase_cache command, identifier expected");
    p.erase_cached_definition(n);
    return p.env();
}

static environment local_cmd(parser & p) {
    if (p.curr_is_token_or_id(get_attribute_tk())) {
        p.next();
        return local_attribute_cmd(p);
    } else {
        return local_notation_cmd(p);
    }
}

static environment help_cmd(parser & p) {
    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
        p.ios().get_regular_stream() << "help result:\n";
    }
    if (p.curr_is_token_or_id(get_options_tk())) {
        p.next();
        auto decls = get_option_declarations();
        decls.for_each([&](name const &, option_declaration const & opt) {
                p.ios().get_regular_stream()
                    << "  " << opt.get_name() << " (" << opt.kind() << ") "
                    << opt.get_description() << " (default: " << opt.get_default_value() << ")" << std::endl;
            });
    } else if (p.curr_is_token_or_id(get_commands_tk())) {
        p.next();
        buffer<name> ns;
        cmd_table const & cmds = p.cmds();
        cmds.for_each([&](name const & n, cmd_info const &) {
                ns.push_back(n);
            });
        std::sort(ns.begin(), ns.end());
        for (name const & n : ns) {
            p.ios().get_regular_stream()
                << "  " << n << ": " << cmds.find(n)->get_descr() << std::endl;
        };
    } else {
        p.ios().get_regular_stream()
            << "help options  : describe available options\n"
            << "help commands : describe available commands\n";
    }
    return p.env();
}

static environment init_quotient_cmd(parser & p) {
    if (!(p.env().prop_proof_irrel() && p.env().impredicative()))
        throw parser_error("invalid init_quotient command, this command is only available for kernels containing an impredicative and proof irrelevant Prop", p.cmd_pos());
    return module::declare_quotient(p.env());
}

static environment init_hits_cmd(parser & p) {
    if (p.env().prop_proof_irrel() || p.env().impredicative())
        throw parser_error("invalid init_hits command, this command is only available for proof relevant and predicative kernels", p.cmd_pos());
    return module::declare_hits(p.env());
}

// register_simp_ext <head> <simp_ext_name> ([priority <prio>])
static environment register_simp_ext_cmd(parser & p) {
    environment env = p.env();
    name head = p.check_constant_next("invalid #register_simp_ext_cmd command, constant expected");
    name simp_ext_name = p.check_constant_next("invalid #register_simp_ext_cmd command, constant expected");

    unsigned prio = LEAN_DEFAULT_PRIORITY;
    auto pos = p.pos();
    decl_attributes attrs;
    attrs.parse(p);
    if (auto const & entry = head_opt(attrs.get_entries()))
        throw parser_error(sstream() << "invalid #register_simp_ext_cmd command, unexpected attribute ["
                                     << entry->m_attr->get_name() << "]", pos);
    if (attrs.get_priority())
        prio = *attrs.get_priority();
    bool persistent = true;
    env = add_simp_extension(env, p.ios(), head, simp_ext_name, prio, persistent);
    return env;
}

/*
   Temporary procedure that converts metavariables in \c e to metavar_context metavariables.
   After we convert the frontend to type_context, we will not need to use this procedure.
*/
static expr convert_metavars(metavar_context & ctx, expr const & e) {
    expr_map<expr> cache;

    std::function<expr(expr const & e)> convert = [&](expr const & e) {
        return replace(e, [&](expr const e, unsigned) {
                if (is_metavar(e)) {
                    auto it = cache.find(e);
                    if (it != cache.end())
                        return some_expr(it->second);
                    expr m = ctx.mk_metavar_decl(local_context(), convert(mlocal_type(e)));
                    cache.insert(mk_pair(e, m));
                    return some_expr(m);
                } else {
                    return none_expr();
                }
            });
    };
    return convert(e);
}

static environment unify_cmd(parser & p) {
    environment const & env = p.env();
    expr e1; level_param_names ls1;
    std::tie(e1, ls1) = parse_local_expr(p);
    p.check_token_next(get_comma_tk(), "invalid #unify command, proper usage \"#unify e1, e2\"");
    expr e2; level_param_names ls2;
    std::tie(e2, ls2) = parse_local_expr(p);
    metavar_context mctx;
    local_context   lctx;
    e1 = convert_metavars(mctx, e1);
    e2 = convert_metavars(mctx, e2);
    tout() << e1 << " =?= " << e2 << "\n";
    type_context ctx(env, p.get_options(), mctx, lctx, transparency_mode::Semireducible);
    bool success = ctx.is_def_eq(e1, e2);
    if (success)
        tout() << ctx.instantiate_mvars(e1) << " =?= " << ctx.instantiate_mvars(e2) << "\n";
    flycheck_information info(p.ios());
    if (info.enabled()) {
        p.display_information_pos(p.cmd_pos());
    }
    p.ios().get_regular_stream() << (success ? "success" : "fail") << std::endl;
    return env;
}

static environment compile_cmd(parser & p) {
    auto pos = p.pos();
    name n = p.check_constant_next("invalid #compile command, constant expected");
    declaration d = p.env().get(n);
    if (!d.is_definition())
        throw parser_error("invalid #compile command, declaration is not a definition", pos);
    return vm_compile(p.env(), d);
}

static environment compile_expr(environment const & env, name const & n, level_param_names const & ls, expr const & type, expr const & e) {
    environment new_env = env;
    bool use_conv_opt   = true;
    bool is_trusted     = false;
    auto cd = check(new_env, mk_definition(new_env, n, ls, type, e, use_conv_opt, is_trusted));
    new_env = new_env.add(cd);
    return vm_compile(new_env, new_env.get(n));
}

static void vm_eval_core(vm_state & s, name const & main, optional<vm_obj> const & initial_state) {
    if (initial_state) s.push(*initial_state); // push initial_state for IO/tactic monad.
    vm_decl d = *s.get_decl(main);
    if (!initial_state && d.get_arity() > 0)
        throw exception("vm_eval result is a function");
    s.invoke_fn(main);
    if (initial_state) {
        if (d.get_arity() == 0) {
            /* main returned a closure, it did not process initial_state yet.
               So, we force the execution. */
            s.apply();
        }
    }
}

static environment vm_eval_cmd(parser & p) {
    auto pos = p.pos();
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p);
    if (has_metavar(e))
        throw parser_error("invalid vm_eval command, expression contains metavariables", pos);
    type_context tc(p.env(), transparency_mode::All);
    expr type0 = tc.infer(e);
    expr type  = tc.whnf(type0);
    bool is_IO = is_constant(get_app_fn(type), get_IO_name());
    bool is_string = false;
    if (!is_IO) {
        /* Check if resultant type has an instance of has_to_string */
        level lvl  = sort_level(tc.whnf(tc.infer(type)));
        expr has_to_string_type = mk_app(mk_constant(get_ToString_name(), {lvl}), type0);
        optional<expr> to_string_instance = tc.mk_class_instance(has_to_string_type);
        if (to_string_instance) {
            /* Modify the 'program' to (to_string e) */
            e         = mk_app(mk_constant(get_ToString_name(), {lvl}), type0, *to_string_instance, e);
            type      = tc.infer(e);
            is_string = true;
        }
    }
    name main("_main");
    environment new_env = compile_expr(p.env(), main, ls, type, e);
    vm_state s(new_env);
    optional<vm_obj> initial_state;
    if (is_IO) initial_state = mk_vm_simple(0);
    if (p.profiling()) {
        timeit timer(p.ios().get_diagnostic_stream(), "vm_eval time");
        vm_eval_core(s, main, initial_state);
    } else {
        vm_eval_core(s, main, initial_state);
    }
    if (is_IO) {
        // do not print anything
    } else if (is_string) {
        vm_obj r = s.get(0);
        p.ios().get_regular_stream() << to_string(r) << "\n";
    } else {
        /* if it is not IO nor a string, then display object on top of the stack using vm_obj display method */
        vm_obj r = s.get(0);
        display(p.ios().get_regular_stream(), r);
        p.ios().get_regular_stream() << "\n";
    }
    return p.env();
}

static std::string * g_declare_trace_key = nullptr;

environment declare_trace_cmd(parser & p) {
    name cls = p.check_id_next("invalid declare_trace command, identifier expected");
    register_trace_class(cls);
    return module::add(p.env(), *g_declare_trace_key, [=](environment const &, serializer & s) { s << cls; });
}

static void declare_trace_reader(deserializer & d, shared_environment &,
                                 std::function<void(asynch_update_fn const &)> &,
                                 std::function<void(delayed_update_fn const &)> &) {
    name cls;
    d >> cls;
    register_trace_class(cls);
}

environment add_key_equivalence_cmd(parser & p) {
    name h1 = p.check_constant_next("invalid add_key_equivalence command, constant expected");
    name h2 = p.check_constant_next("invalid add_key_equivalence command, constant expected");
    return add_key_equivalence(p.env(), h1, h2);
}

static environment run_command_cmd(parser & p) {
    /* initial state for executing the tactic */
    environment env      = p.env();
    options opts         = p.get_options();
    metavar_context mctx;
    expr tactic          = p.parse_expr();
    expr try_constructor = mk_app(mk_constant(get_Tactic_try_name()), mk_constant(get_Tactic_constructor_name()));
    tactic               = mk_app(mk_constant(get_Monad_andThen_name()), tactic, try_constructor);
    expr val             = mk_typed_expr(mk_true(), mk_by(tactic));
    bool check_unassigned = false;
    elaborate(env, opts, mctx, local_context(), val, check_unassigned);
    return env;
}

void init_cmd_table(cmd_table & r) {
    add_cmd(r, cmd_info("open",              "create aliases for declarations, and use objects defined in other namespaces",
                        open_cmd));
    add_cmd(r, cmd_info("export",            "create aliases for declarations", export_cmd));
    add_cmd(r, cmd_info("set_option",        "set configuration option", set_option_cmd));
    add_cmd(r, cmd_info("exit",              "exit", exit_cmd));
    add_cmd(r, cmd_info("print",             "print a string", print_cmd));
    add_cmd(r, cmd_info("section",           "open a new section", section_cmd));
    add_cmd(r, cmd_info("namespace",         "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",               "close the current namespace/section", end_scoped_cmd));
    add_cmd(r, cmd_info("check",             "type check given expression, and display its type", check_cmd));
    add_cmd(r, cmd_info("eval",              "evaluate given expression", eval_cmd));
    add_cmd(r, cmd_info("vm_eval",           "VM evaluation", vm_eval_cmd));
    add_cmd(r, cmd_info("local",             "define local attributes or notation", local_cmd));
    add_cmd(r, cmd_info("help",              "brief description of available commands and options", help_cmd));
    add_cmd(r, cmd_info("init_quotient",     "initialize quotient type computational rules", init_quotient_cmd));
    add_cmd(r, cmd_info("init_hits",         "initialize builtin HITs", init_hits_cmd));
    add_cmd(r, cmd_info("declare_trace",     "declare a new trace class (for debugging Lean tactics)", declare_trace_cmd));
    add_cmd(r, cmd_info("register_simp_ext", "register simplifier extension", register_simp_ext_cmd));
    add_cmd(r, cmd_info("add_key_equivalence", "register that to symbols are equivalence for key-matching", add_key_equivalence_cmd));
    add_cmd(r, cmd_info("run_command",       "execute an user defined command at top-level", run_command_cmd));
    add_cmd(r, cmd_info("#erase_cache",      "erase cached definition (for debugging purposes)", erase_cache_cmd));
    add_cmd(r, cmd_info("#unify",            "(for debugging purposes)", unify_cmd));
    add_cmd(r, cmd_info("#compile",          "(for debugging purposes)", compile_cmd));

    register_decl_cmds(r);
    register_inductive_cmds(r);
    register_structure_cmd(r);
    register_notation_cmds(r);
    // register_tactic_hint_cmd(r);
}

static cmd_table * g_cmds = nullptr;

cmd_table get_builtin_cmds() {
    return *g_cmds;
}

void initialize_builtin_cmds() {
    g_cmds = new cmd_table();
    init_cmd_table(*g_cmds);
    g_declare_trace_key = new std::string("decl_trace");
    register_module_object_reader(*g_declare_trace_key, declare_trace_reader);
}

void finalize_builtin_cmds() {
    delete g_cmds;
    delete g_declare_trace_key;
}
}
