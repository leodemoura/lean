/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/interrupt.h"
#include "library/parray.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_array.h"

namespace lean {
static void to_string(vm_obj const & o, std::string & s) {
    check_system("to_string");
    parray<vm_obj> const & a = to_array(cfield(o, 1));
    for (size_t i = 0; i < a.size(); i++) {
        s += static_cast<unsigned char>(cidx(a[i]));
    }
}

std::string to_string(vm_obj const & o) {
    std::string r;
    to_string(o, r);
    return r;
}

vm_obj to_obj(std::string const & str) {
    parray<vm_obj> a;
    for (char c : str) {
        a.push_back(mk_vm_simple(c));
    }
    return mk_vm_constructor(2, mk_vm_simple(str.size()), to_obj(a));
}
}
