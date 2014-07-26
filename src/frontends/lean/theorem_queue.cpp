/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/timeit.h"
#include "kernel/type_checker.h"
#include "frontends/lean/theorem_queue.h"
#include "frontends/lean/parser.h"
#ifdef LEAN_USE_FORK
  #include <sys/types.h>
  #include <sys/wait.h>
  #include <stdlib.h>
  #include <unistd.h>
#endif

namespace lean {
#ifdef LEAN_USE_FORK
theorem_queue::theorem_queue(parser & p, unsigned num_threads):m_parser(p), m_num_threads(num_threads) {}
void theorem_queue::add(environment const & env, name const & n, level_param_names const & ls, local_level_decls const & lls,
                        expr const & t, expr const & v) {
    m_queue.emplace_back(env, n, ls, lls, t, v);
}
void theorem_queue::process_theorems(unsigned i) {
    // std::cout << "process: " << i << "\n";
    timeit time(std::cout, "process time");
    environment env; name n; level_param_names ls; local_level_decls lls;
    expr t, v;
    for (unsigned j = 0; j < m_queue.size(); j++) {
        if (j % m_num_threads == i) {
            std::tie(env, n, ls, lls, t, v) = m_queue[j];
            // std::cout << "processing " << n << "[" << i << "]\n";
            level_param_names new_ls;
            expr type, value;
            std::tie(type, value, new_ls) = m_parser.elaborate_definition_at(env, lls, n, t, v);
            check(env, mk_theorem(n, append(ls, new_ls), type, value));
        }
    }
}
std::vector<certified_declaration> const & theorem_queue::join() {
    buffer<pid_t> pids;
    for (unsigned i = 0; i < m_num_threads; i++) {
        pid_t pid = fork();
        if (pid == -1) {
            throw exception("failed to fork process");
        } else if (pid == 0) {
            process_theorems(i);
            _exit(EXIT_SUCCESS);
        } else {
            pids.push_back(pid);
        }
    }
    for (auto const & pid : pids) {
        int status;
        waitpid(pid, &status, 0);
    }
    return m_result;
}
void theorem_queue::interrupt() {}
bool theorem_queue::done() const {
    return true;
}
#else
// Implementation using threads.
theorem_queue::theorem_queue(parser & p, unsigned num_threads):
    m_parser(p),
    m_queue(num_threads > 1 ? num_threads - 1 : 0, []() { enable_expr_caching(false); }) {}
void theorem_queue::add(environment const & env, name const & n, level_param_names const & ls, local_level_decls const & lls,
                        expr const & t, expr const & v) {
    m_queue.add([=]() {
            level_param_names new_ls;
            expr type, value;
            std::tie(type, value, new_ls) = m_parser.elaborate_definition_at(env, lls, n, t, v);
            return check(env, mk_theorem(n, append(ls, new_ls), type, value));
        });
}
std::vector<certified_declaration> const & theorem_queue::join() { return m_queue.join(); }
void theorem_queue::interrupt() { m_queue.interrupt(); }
bool theorem_queue::done() const { return m_queue.done(); }
#endif
}
