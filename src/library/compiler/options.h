/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch, and Leonardo de Moura
*/
#pragma once
#include "util/sexpr/options.h"

namespace lean {
namespace native {
/** \brief Blast configuration object. */
struct config {
    char const * m_native_library_path;
    char const * m_native_main_fn;
    
    // unsigned                   m_max_depth;
    // unsigned                   m_init_depth;
    // unsigned                   m_inc_depth;
    // bool                       m_subst;
    // bool                       m_simp;
    // bool                       m_recursor;
    // bool                       m_ematch;
    // bool                       m_cc;
    // bool                       m_backward;
    // bool                       m_show_failure;
    // char const *               m_strategy;
    // unsigned                   m_pattern_max_steps;
    config(options const & o);
};

struct scope_config {
    config * m_old;
    config m_config;
public:
    scope_config(options const & o);
    ~scope_config();
};

config & get_config();

void initialize_options();
void finalize_options();
}}
