/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#define LEAN_USE_FORK
#pragma once
#include "kernel/environment.h"
#include "frontends/lean/local_decls.h"
#ifndef LEAN_USE_FORK
#include "util/worker_queue.h"
#endif

namespace lean {
class parser;
typedef local_decls<level>  local_level_decls;
class theorem_queue {
    parser & m_parser;
    #ifdef LEAN_USE_FORK
        unsigned m_num_threads;
        std::vector<std::tuple<environment, name, level_param_names, local_level_decls, expr, expr>> m_queue;
        std::vector<certified_declaration> m_result;
        void process_theorems(unsigned i);
    #else
        worker_queue<certified_declaration> m_queue;
    #endif
public:
    theorem_queue(parser & p, unsigned num_threads);
    void add(environment const & env, name const & n, level_param_names const & ls, local_level_decls const & lls,
             expr const & t, expr const & v);
    std::vector<certified_declaration> const & join();
    void interrupt();
    bool done() const;
};
}
