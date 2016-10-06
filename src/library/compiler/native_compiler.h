/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#pragma once
#include "kernel/environment.h"


namespace lean {

void set_install_path(std::string s);
std::string get_install_path();

struct extern_fn;

enum native_compiler_mode { JIT, AOT };
void native_compile(environment const & env, buffer<pair<name, expr>> & procs, native_compiler_mode & mode);
void native_compile_binary(environment const & env, declaration const & d);
void native_compile_module(environment const & env, buffer<declaration> decls);
// void native_aot_compile(environment const & env, config & conf, declaration const & main);
// void native_compile_file(environment const & env, config & conf, declaration const & main);
void initialize_native_compiler();
void finalize_native_compiler();
}
