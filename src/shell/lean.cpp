/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <fstream>
#include <signal.h>
#include <cstdlib>
#include <getopt.h>
#include <string>
#include "util/stackinfo.h"
#include "util/macros.h"
#include "util/debug.h"
#include "util/sstream.h"
#include "util/interrupt.h"
#include "util/memory.h"
#include "util/thread.h"
#include "util/lean_path.h"
#include "util/file_lock.h"
#include "util/sexpr/options.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/type_checker.h"
#include "kernel/formatter.h"
#include "library/standard_kernel.h"
#include "library/module.h"
#include "library/flycheck.h"
#include "library/type_context.h"
#include "library/io_state_stream.h"
#include "library/definition_cache.h"
#include "library/export.h"
#include "library/error_handling.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/dependencies.h"
#include "frontends/lean/opt_cmd.h"
#include "frontends/smt2/parser.h"
#include "library/compiler/options.h"
#include "library/compiler/native_compiler.h"
#include "init/init.h"
#include "shell/emscripten.h"
#include "shell/simple_pos_info_provider.h"
#include "version.h"
#include "githash.h" // NOLINT

using lean::unreachable_reached;
using lean::environment;
using lean::io_state;
using lean::io_state_stream;
using lean::regular;
using lean::mk_environment;
using lean::definition_cache;
using lean::pos_info;
using lean::pos_info_provider;
using lean::optional;
using lean::expr;
using lean::options;
using lean::module_name;
using lean::simple_pos_info_provider;
using lean::shared_file_lock;
using lean::exclusive_file_lock;
using lean::type_context;
using lean::type_checker;

static void display_header(std::ostream & out) {
    out << "Lean (version " << LEAN_VERSION_MAJOR << "."
        << LEAN_VERSION_MINOR << "." << LEAN_VERSION_PATCH;
    if (std::strcmp(g_githash, "GITDIR-NOTFOUND") == 0) {
        if (std::strcmp(LEAN_PACKAGE_VERSION, "NOT-FOUND") != 0) {
            out << ", package " << LEAN_PACKAGE_VERSION;
        }
    } else {
        out << ", commit " << std::string(g_githash).substr(0, 12);
    }
    out << ", " << LEAN_STR(LEAN_BUILD_TYPE) << ")\n";
}

static void display_help(std::ostream & out) {
    display_header(out);
    std::cout << "Input format:\n";
    std::cout << "  --smt2            interpret files as SMT-Lib2 files\n";
    std::cout << "Miscellaneous:\n";
    std::cout << "  --help -h         display this message\n";
    std::cout << "  --version -v      display version number\n";
    std::cout << "  --githash         display the git commit hash number used to build this binary\n";
    std::cout << "  --path            display the path used for finding Lean libraries and extensions\n";
    std::cout << "  --output=file -o  save the final environment in binary format in the given file\n";
    std::cout << "  --trust=num -t    trust level (default: max) 0 means do not trust any macro,\n"
              << "                    and type check all imported modules\n";
    std::cout << "  --quiet -q        do not print verbose messages\n";
#if defined(LEAN_TRACK_MEMORY)
    std::cout << "  --memory=num -M   maximum amount of memory that should be used by Lean\n";
    std::cout << "                    (in megabytes)\n";
#endif
#if defined(LEAN_MULTI_THREAD)
    std::cout << "  --threads=num -j  number of threads used to process lean files\n";
#endif
    std::cout << "  --deps            just print dependencies of a Lean input\n";
    std::cout << "  --flycheck        print structured error message for flycheck\n";
    std::cout << "  --cache=file -c   load/save cached definitions from/to the given file\n";
    std::cout << "  --profile         display elaboration/type checking time for each definition/theorem\n";
#if defined(LEAN_USE_BOOST)
    std::cout << "  --tstack=num -s   thread stack size in Kb\n";
#endif
    DEBUG_CODE(
    std::cout << "  --debug=tag       enable assertions with the given tag\n";
        )
    std::cout << "  -D name=value     set a configuration option (see set_option command)\n";
    std::cout << "  --dir=directory   display information about identifier or token in the given posivition\n";
    std::cout << "Frontend query interface:\n";
    std::cout << "  --line=value      line number for query\n";
    std::cout << "  --col=value       column number for query\n";
    std::cout << "  --goal            display goal at close to given position\n";
    std::cout << "  --hole            display type of the \"hole\" in the given posivition\n";
    std::cout << "  --info            display information about identifier or token in the given posivition\n";
    std::cout << "Exporting data:\n";
    std::cout << "  --export=file -E  export final environment as textual low-level file\n";
    std::cout << "  --export-all=file -A  export final environment (and all dependencies) as textual low-level file\n";
}

static struct option g_long_options[] = {
    {"version",      no_argument,       0, 'v'},
    {"help",         no_argument,       0, 'h'},
    {"smt2",         no_argument,       0, 'Y'},
    {"path",         no_argument,       0, 'p'},
    {"githash",      no_argument,       0, 'g'},
    {"output",       required_argument, 0, 'o'},
    {"native",       required_argument, 0, 'n'},
    {"export",       required_argument, 0, 'E'},
    {"export-all",   required_argument, 0, 'A'},
    {"memory",       required_argument, 0, 'M'},
    {"trust",        required_argument, 0, 't'},
    {"profile",      no_argument,       0, 'P'},
    {"compile",      optional_argument, 0, 'C'},
    // {"main_fn",      required_argument, 0, 'M'}, optional_arg?
#if defined(LEAN_MULTI_THREAD)
    {"threads",      required_argument, 0, 'j'},
#endif
    {"quiet",        no_argument,       0, 'q'},
    {"cache",        required_argument, 0, 'c'},
    {"deps",         no_argument,       0, 'd'},
    {"flycheck",     no_argument,       0, 'F'},
#if defined(LEAN_USE_BOOST)
    {"tstack",       required_argument, 0, 's'},
#endif
    {"line",         required_argument, 0, 'L'},
    {"col",          required_argument, 0, 'O'},
    {"goal",         no_argument,       0, 'G'},
    {"hole",         no_argument,       0, 'Z'},
    {"info",         no_argument,       0, 'I'},
    {"dir",          required_argument, 0, 'T'},
#ifdef LEAN_DEBUG
    {"debug",        required_argument, 0, 'B'},
#endif
    {"dir",          required_argument, 0, 'T'},
    {0, 0, 0, 0}
};

#define OPT_STR "PFdD:qupgvhk:012t:012o:E:c:L:012O:012GZAIT:B:"

#if defined(LEAN_TRACK_MEMORY)
#define OPT_STR2 OPT_STR "M:012"
#else
#define OPT_STR2 OPT_STR
#endif

#if defined(LEAN_USE_BOOST) && defined(LEAN_MULTI_THREAD)
static char const * g_opt_str = OPT_STR2 "j:012s:012";
#elif !defined(LEAN_USE_BOOST) && defined(LEAN_MULTI_THREAD)
static char const * g_opt_str = OPT_STR2 "j:012";
#else
static char const * g_opt_str = OPT_STR2;
#endif

options set_config_option(options const & opts, char const * in) {
    if (!in) return opts;
    while (*in && std::isspace(*in))
        ++in;
    std::string in_str(in);
    auto pos = in_str.find('=');
    if (pos == std::string::npos)
        throw lean::exception("invalid -D parameter, argument must contain '='");
    lean::name opt = lean::string_to_name(in_str.substr(0, pos));
    std::string val = in_str.substr(pos+1);
    auto decls = lean::get_option_declarations();
    auto it = decls.find(opt);
    if (it) {
        switch (it->kind()) {
        case lean::BoolOption:
            if (val == "true")
                return opts.update(opt, true);
            else if (val == "false")
                return opts.update(opt, false);
            else
                throw lean::exception(lean::sstream() << "invalid -D parameter, invalid configuration option '" << opt
                                      << "' value, it must be true/false");
        case lean::IntOption:
        case lean::UnsignedOption:
            return opts.update(opt, atoi(val.c_str()));
        case lean::StringOption:
            return opts.update(opt, val);
        default:
            throw lean::exception(lean::sstream() << "invalid -D parameter, configuration option '" << opt
                                  << "' cannot be set in the command line, use set_option command");
        }
    } else {
        throw lean::exception(lean::sstream() << "invalid -D parameter, unknown configuration option '" << opt << "'");
    }
}

#if defined(LEAN_EMSCRIPTEN)
#include <emscripten/bind.h>
EMSCRIPTEN_BINDINGS(LEAN_JS) {
    emscripten::function("lean_init", &initialize_emscripten);
    emscripten::function("lean_import_module", &emscripten_import_module);
    emscripten::function("lean_process_file", &emscripten_process_file);
}
int main() { return 0; }
#else
int main(int argc, char ** argv) {
    lean::initializer init;
    lean::set_install_path(argv[0]);
    bool export_objects     = false;
    bool export_native_objects = false;
    unsigned trust_lvl      = LEAN_BELIEVER_TRUST_LEVEL+1;
    bool smt2               = false;
    bool compile            = false;
    bool only_deps          = false;
    unsigned num_threads    = 1;
    bool read_cache         = false;
    bool save_cache         = false;
    options opts;
    std::string output;
    std::string native_output;
    std::string cache_name;
    optional<unsigned> line;
    optional<unsigned> column;
    optional<std::string> export_txt;
    optional<std::string> export_all_txt;
    optional<std::string> base_dir;
    bool show_goal = false;
    bool show_hole = false;
    bool show_info = false;
    while (true) {
        int c = getopt_long(argc, argv, g_opt_str, g_long_options, NULL);
        if (c == -1)
            break; // end of command line
        switch (c) {
        case 'j':
            num_threads = atoi(optarg);
            break;
        case 'v':
            display_header(std::cout);
            return 0;
        case 'g':
            std::cout << g_githash << "\n";
            return 0;
        case 'h':
            display_help(std::cout);
            return 0;
        case 'Y':
            smt2 = true;
            break;
        case 'p':
            std::cout << lean::get_lean_path() << "\n";
            return 0;
        case 's':
            lean::set_thread_stack_size(atoi(optarg)*1024);
            break;
        case 'o':
            output         = optarg;
            export_objects = true;
            break;
        case 'n':
            native_output         = optarg;
            export_native_objects = true;
            break;
        case 'c':
            cache_name = optarg;
            read_cache = true;
            save_cache = true;
            break;
        case 'M':
            lean::set_max_memory_megabyte(atoi(optarg));
            opts = opts.update(lean::get_max_memory_opt_name(), atoi(optarg));
            break;
        case 't':
            trust_lvl = atoi(optarg);
            break;
        case 'q':
            opts = opts.update(lean::get_verbose_opt_name(), false);
            break;
        case 'd':
            only_deps = true;
            break;
        case 'D':
            try {
                opts = set_config_option(opts, optarg);
            } catch (lean::exception & ex) {
                std::cerr << ex.what() << std::endl;
                return 1;
            }
            break;
        case 'F':
            opts = opts.update("flycheck", true);
            break;
        case 'P':
            opts = opts.update("profile", true);
            break;
        case 'L':
            line = atoi(optarg);
            break;
        case 'O':
            column = atoi(optarg);
            break;
        case 'G':
            show_goal = true;
            break;
        case 'Z':
            show_hole = true;
            break;
        case 'I':
            show_info = true;
            break;
        case 'E':
            export_txt = std::string(optarg);
            break;
        case 'C':
            compile = true;
            break;
#ifdef LEAN_DEBUG
        case 'B':
            lean::enable_debug(optarg);
            break;
#endif
        case 'A':
            export_all_txt = std::string(optarg);
            break;
        case 'T':
            base_dir = std::string(optarg);
            break;
        default:
            std::cerr << "Unknown command line option\n";
            display_help(std::cerr);
            return 1;
        }
    }

    #if defined(__GNUC__) && !defined(__CLANG__)
    #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
    #endif
    if (show_hole && line && column) {
        opts       = set_show_hole(opts, *line, *column);
        save_cache = false;
    } else if (show_goal && line && column) {
        opts       = set_show_goal(opts, *line, *column);
        save_cache = false;
    } else if (show_info && line && column) {
        opts       = set_show_info(opts, *line, *column);
        save_cache = false;
    }

    #if !defined(LEAN_MULTI_THREAD)
    lean_assert(num_threads == 1);
    #endif

    if (smt2) {
        // Note: the smt2 flag may override other flags
        environment env = mk_environment(trust_lvl);
        io_state ios(opts, lean::mk_pretty_formatter_factory());
        bool ok = true;
        for (int i = optind; i < argc; i++) {
            try {
                ok = ::lean::smt2::parse_commands(env, ios, argv[i]);
            } catch (lean::exception & ex) {
                ok = false;
                type_context tc(env, ios.get_options());
                auto out = diagnostic(env, ios, tc);
                simple_pos_info_provider pp(argv[i]);
                lean::display_error(out, &pp, ex);
            }
        }
        return ok ? 0 : 1;
    }

    environment env = mk_environment(trust_lvl);
    io_state ios(opts, lean::mk_pretty_formatter_factory());
    definition_cache   cache;
    definition_cache * cache_ptr = nullptr;
    if (read_cache) {
        try {
            cache_ptr = &cache;
            shared_file_lock cache_lock(cache_name);
            std::ifstream in(cache_name, std::ifstream::binary);
            if (!in.bad() && !in.fail())
                cache.load(in);
        } catch (lean::throwable & ex) {
            cache_ptr = nullptr;
            // I'm using flycheck_error instead off flycheck_warning because
            // the :error-patterns at lean-flycheck.el do not work after
            // I add a rule for FLYCHECK_WARNING.
            // Same for display_error_pos vs display_warning_pos.
            lean::flycheck_error warn(ios);
            if (optind < argc)
                display_error_pos(ios.get_regular_stream(), ios.get_options(), argv[optind], 1, 0);
            ios.get_regular_stream()
                << "failed to load cache file '" << cache_name << "', "
                << ex.what() << ". cache is going to be ignored\n";
        }
    }
    try {
        bool ok = true;
        for (int i = optind; i < argc; i++) {
            try {
                if (only_deps) {
                    if (!display_deps(env, std::cout, std::cerr, argv[i]))
                        ok = false;
                } else if (!parse_commands(env, ios, argv[i], base_dir, false, num_threads,
                                           cache_ptr)) {
                    ok = false;
                }
            } catch (lean::exception & ex) {
                simple_pos_info_provider pp(argv[i]);
                ok = false;
                type_context tc(env, ios.get_options());
                auto out = diagnostic(env, ios, tc);
                lean::display_error(out, &pp, ex);
            }
        }


        if (ok && compile && default_k == input_kind::Lean) {
            if (default_k == input_kind::Lean) {
                lean::native::scope_config scoped_native_config(ios.get_options());
                native_compile_binary(env, env.get(lean::name("main")));
            } else {
                // Not sure the right way to report this error.
                std::cout << "can't not natively compile .hlean files" << std::endl;
                exit(1);
            }
        }
        if (ok && server && (default_k == input_kind::Lean || default_k == input_kind::HLean)) {
            signal(SIGINT, on_ctrl_c);
            ios.set_option(lean::name("pp", "beta"), true);
            lean::server Sv(env, ios, base_dir, num_threads);
            if (!Sv(std::cin))
                ok = false;
        }
        if (save_cache) {
            exclusive_file_lock cache_lock(cache_name);
            std::ofstream out(cache_name, std::ofstream::binary);
            cache.save(out);
        }
        if (export_objects && ok) {
            exclusive_file_lock output_lock(output);
            std::ofstream out(output, std::ofstream::binary);
            export_module(out, env);
        }
        if (export_native_objects && ok && default_k == input_kind::Lean) {
            exclusive_file_lock output_lock(native_output);
            std::ofstream out(native_output, std::ofstream::binary);
            export_native_module(out, env);
        }
        if (export_txt) {
            exclusive_file_lock expor_lock(*export_txt);
            std::ofstream out(*export_txt);
            export_module_as_lowtext(out, env);
        }
        if (export_all_txt) {
            exclusive_file_lock export_lock(*export_all_txt);
            std::ofstream out(*export_all_txt);
            export_all_as_lowtext(out, env);
        }
        return ok ? 0 : 1;
    } catch (lean::throwable & ex) {
        type_context tc(env, ios.get_options());
        auto out = diagnostic(env, ios, tc);
        lean::display_error(out, nullptr, ex);
    } catch (std::bad_alloc & ex) {
        std::cerr << "out of memory" << std::endl;
        return 1;
    }
    return 1;
}
#endif
