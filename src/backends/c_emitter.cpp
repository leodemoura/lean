    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "c_emitter.h"
#include "kernel/environment.h"
#include "kernel/inductive/inductive.h"
#include "kernel/instantiate.h"
#include "used_names.h"
#include "util/name.h"
#include "util/name_set.h"

namespace lean {

c_emitter::c_emitter() : m_output_stream(std::cout) {}

c_emitter::c_emitter(std::string output_file)
    : m_output_stream(fstream(output_file, std::ios_base::out)) {}

void c_emitter::emit_return(simple_expr const & se) {
}
