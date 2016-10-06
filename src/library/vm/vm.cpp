/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/

#include <string>
#include <algorithm>
#include <vector>
#include "util/flet.h"
#include "util/interrupt.h"
#include "util/sstream.h"
#include "util/small_object_allocator.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/trace.h"
#include "library/module.h"
#include "library/vm/vm.h"
#include "library/vm/vm_expr.h"

namespace lean {
void vm_obj_cell::dec_ref(vm_obj & o, buffer<vm_obj_cell*> & todelete) {
    if (LEAN_VM_IS_PTR(o.m_data)) {
        vm_obj_cell * c = o.steal_ptr();
        if (c->dec_ref_core())
            todelete.push_back(c);
    }
}

MK_THREAD_LOCAL_GET(small_object_allocator, get_small_allocator, "vm object");

small_object_allocator & get_vm_allocator() {
    return get_small_allocator();
}

vm_composite::vm_composite(vm_obj_kind k, unsigned idx, unsigned sz, vm_obj const * data):
    vm_obj_cell(k), m_idx(idx),  m_size(sz) {
    vm_obj * fields = get_field_ptr();
    std::uninitialized_copy(data, data + sz, fields);
}

static vm_obj mk_vm_composite(vm_obj_kind k, unsigned idx, unsigned sz, vm_obj const * data) {
    lean_assert(k == vm_obj_kind::Constructor || k == vm_obj_kind::Closure);
    return vm_obj(new (get_small_allocator().allocate(sizeof(vm_composite) + sz * sizeof(vm_obj))) vm_composite(k, idx, sz, data));
}

void vm_composite::dealloc(buffer<vm_obj_cell*> & todelete) {
    unsigned sz = m_size;
    vm_obj * fields = get_field_ptr();
    for (unsigned i = 0; i < sz; i++) {
        dec_ref(fields[i], todelete);
    }
    this->~vm_composite();
    get_small_allocator().deallocate(sizeof(vm_composite) + sz * sizeof(vm_obj), this);
}

vm_obj mk_vm_constructor(unsigned cidx, unsigned sz, vm_obj const * data) {
    return mk_vm_composite(vm_obj_kind::Constructor, cidx, sz, data);
}

vm_obj mk_vm_constructor(unsigned cidx, std::initializer_list<vm_obj const> args) {
    return mk_vm_constructor(cidx, args.size(), args.begin());
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1) {
    return mk_vm_constructor(cidx, 1, &o1);
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1, vm_obj const & o2) {
    vm_obj args[2] = {o1, o2};
    return mk_vm_constructor(cidx, 2, args);
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3) {
    vm_obj args[3] = {o1, o2, o3};
    return mk_vm_constructor(cidx, 3, args);
}

vm_obj mk_vm_constructor(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3, vm_obj const & o4) {
    vm_obj args[4] = {o1, o2, o3, o4};
    return mk_vm_constructor(cidx, 4, args);
}

vm_obj mk_native_closure(environment const & env, name const & n, std::initializer_list<vm_obj const> args) {
    return mk_native_closure(env, n, args.size(), args.begin());
}

vm_obj mk_native_closure(environment const & env, name const & n, unsigned sz, vm_obj const * data) {
      unsigned idx = *lean::get_vm_constant_idx(env, n);
      return lean::mk_vm_closure(idx, sz, data);
}

vm_obj mk_vm_closure(unsigned fn_idx, unsigned sz, vm_obj const * data) {
    return mk_vm_composite(vm_obj_kind::Closure, fn_idx, sz, data);
}

vm_obj mk_vm_closure(unsigned cidx, vm_obj const & o1) {
    return mk_vm_closure(cidx, 1, &o1);
}

vm_obj mk_vm_closure(unsigned cidx, vm_obj const & o1, vm_obj const & o2) {
    vm_obj args[2] = {o1, o2};
    return mk_vm_closure(cidx, 2, args);
}

vm_obj mk_vm_closure(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3) {
    vm_obj args[3] = {o1, o2, o3};
    return mk_vm_closure(cidx, 3, args);
}

vm_obj mk_vm_closure(unsigned cidx, vm_obj const & o1, vm_obj const & o2, vm_obj const & o3, vm_obj const & o4) {
    vm_obj args[4] = {o1, o2, o3, o4};
    return mk_vm_closure(cidx, 4, args);
}

vm_mpz::vm_mpz(mpz const & v):
    vm_obj_cell(vm_obj_kind::MPZ),
    m_value(v) {
}

vm_obj mk_vm_simple(unsigned v) {
    return vm_obj(v);
}

vm_obj mk_vm_mpz(mpz const & v) {
    return vm_obj(new (get_small_allocator().allocate(sizeof(vm_mpz))) vm_mpz(v));
}

void vm_mpz::dealloc() {
    this->~vm_mpz();
    get_small_allocator().deallocate(sizeof(vm_mpz), this);
}

void vm_obj_cell::dealloc() {
    try {
        buffer<vm_obj_cell*> todo;
        todo.push_back(this);
        while (!todo.empty()) {
            vm_obj_cell * it = todo.back();
            todo.pop_back();
            lean_assert(it->get_rc() == 0);
            switch (it->kind()) {
            case vm_obj_kind::Simple:      lean_unreachable();
            case vm_obj_kind::Constructor: to_composite(it)->dealloc(todo); break;
            case vm_obj_kind::Closure:     to_composite(it)->dealloc(todo); break;
            case vm_obj_kind::MPZ:         to_mpz_core(it)->dealloc(); break;
            case vm_obj_kind::External:    to_external(it)->dealloc(); break;
            }
        }
    } catch (std::bad_alloc&) {
        // We need this catch, because push_back may fail when expanding the buffer.
        // In this case, we avoid the crash, and "accept" the memory leak.
    }
}

void display(std::ostream & out, vm_obj const & o, std::function<optional<name>(unsigned)> const & idx2name) {
    if (is_simple(o)) {
        out << cidx(o);
    } else if (is_constructor(o)) {
        out << "(#" << cidx(o);
        for (unsigned i = 0; i < csize(o); i++) {
            out << " ";
            display(out, cfield(o, i), idx2name);
        }
        out << ")";
    } else if (is_mpz(o)) {
        out << to_mpz(o);
    } else if (is_external(o)) {
        out << "[external]";
    } else if (is_closure(o)) {
        if (auto n = idx2name(cfn_idx(o))) {
            out << "(" << *n;
        } else {
            out << "(fn#" << cfn_idx(o);
        }
        for (unsigned i = 0; i < csize(o); i++) {
            out << " ";
            display(out, cfield(o, i), idx2name);
        }
        out << ")";
    } else {
        out << "[unknown]";
    }
}

void display(std::ostream & out, vm_obj const & o) {
    display(out, o, [](unsigned) { return optional<name>(); });
}

static void display_fn(std::ostream & out, std::function<optional<name>(unsigned)> const & idx2name, unsigned fn_idx) {
    if (auto r = idx2name(fn_idx))
        out << *r;
    else
        out << fn_idx;
}

static void display_builtin_cases(std::ostream & out, std::function<optional<name>(unsigned)> const & idx2name, unsigned cases_idx) {
    display_fn(out, idx2name, cases_idx);
}

void vm_instr::display(std::ostream & out,
                       std::function<optional<name>(unsigned)> const & idx2name,
                       std::function<optional<name>(unsigned)> const & cases_idx2name) const {
    switch (m_op) {
    case opcode::Push:          out << "push " << m_idx; break;
    case opcode::Ret:           out << "ret"; break;
    case opcode::Drop:          out << "drop " << m_num; break;
    case opcode::Goto:          out << "goto " << m_pc[0]; break;
    case opcode::SConstructor:  out << "scnstr #" << m_cidx; break;
    case opcode::Constructor:   out << "cnstr #" << m_cidx << " " << m_nfields; break;
    case opcode::Num:           out << "num " << *m_mpz; break;
    case opcode::Unreachable:   out << "unreachable"; break;
    case opcode::Destruct:      out << "destruct"; break;
    case opcode::Cases2:        out << "cases2 " << m_pc[1]; break;
    case opcode::CasesN:
        out << "cases";
        for (unsigned i = 0; i < get_casesn_size(); i++)
            out << " " << get_casesn_pc(i);
        break;
    case opcode::BuiltinCases:
        out << "builtin_cases ";
        display_builtin_cases(out, cases_idx2name, get_cases_idx());
        out << ",";
        for (unsigned i = 0; i < get_casesn_size(); i++)
            out << " " << get_casesn_pc(i);
        break;
    case opcode::NatCases:      out << "nat_cases " << m_pc[1]; break;
    case opcode::Proj:          out << "proj " << m_idx; break;
    case opcode::Apply:         out << "apply"; break;
    case opcode::InvokeGlobal:
        out << "ginvoke ";
        display_fn(out, idx2name, m_fn_idx);
        break;
    case opcode::InvokeBuiltin:
        out << "builtin ";
        display_fn(out, idx2name, m_fn_idx);
        break;
    case opcode::InvokeCFun:
        out << "cfun ";
        display_fn(out, idx2name, m_fn_idx);
        break;
    case opcode::Closure:
        out << "closure ";
        display_fn(out, idx2name, m_fn_idx);
        out << " " << m_nargs;
        break;
    case opcode::Pexpr:
        out << "pexpr " << *m_expr; break;
    }
}

void vm_instr::display(std::ostream & out) const {
    display(out, [](unsigned) { return optional<name>(); }, [](unsigned) { return optional<name>(); });
}

unsigned vm_instr::get_num_pcs() const {
    switch (m_op) {
    case opcode::Goto:
        return 1;
    case opcode::Cases2: case opcode::NatCases:
        return 2;
    case opcode::CasesN: case opcode::BuiltinCases:
        return get_casesn_size();
    default:
        return 0;
    }
}

unsigned vm_instr::get_pc(unsigned i) const {
    lean_assert(i < get_num_pcs());
    switch (m_op) {
    case opcode::Goto:
    case opcode::Cases2: case opcode::NatCases:
        return m_pc[i];
    case opcode::CasesN: case opcode::BuiltinCases:
        return get_casesn_pc(i);
    default:
        lean_unreachable();
    }
}

void vm_instr::set_pc(unsigned i, unsigned pc) {
    lean_assert(i < get_num_pcs());
    switch (m_op) {
    case opcode::Goto:
    case opcode::Cases2: case opcode::NatCases:
        m_pc[i] = pc;
        break;
    case opcode::CasesN: case opcode::BuiltinCases:
        set_casesn_pc(i, pc);
        break;
    default:
        lean_unreachable();
    }
}

vm_instr mk_push_instr(unsigned idx) {
    vm_instr r(opcode::Push);
    r.m_idx = idx;
    return r;
};

vm_instr mk_drop_instr(unsigned n) {
    vm_instr r(opcode::Drop);
    r.m_num = n;
    return r;
}

vm_instr mk_proj_instr(unsigned n) {
    vm_instr r(opcode::Proj);
    r.m_idx = n;
    return r;
}

vm_instr mk_goto_instr(unsigned pc) {
    vm_instr r(opcode::Goto);
    r.m_pc[0] = pc;
    return r;
}

vm_instr mk_sconstructor_instr(unsigned cidx) {
    vm_instr r(opcode::SConstructor);
    r.m_cidx = cidx;
    return r;
}

vm_instr mk_constructor_instr(unsigned cidx, unsigned nfields) {
    vm_instr r(opcode::Constructor);
    r.m_cidx    = cidx;
    r.m_nfields = nfields;
    return r;
}

vm_instr mk_num_instr(mpz const & v) {
    if (v < LEAN_MAX_SMALL_NAT) {
        vm_instr r(opcode::SConstructor);
        r.m_num = v.get_unsigned_int();
        return r;
    } else {
        vm_instr r(opcode::Num);
        r.m_mpz = new mpz(v);
        return r;
    }
}

vm_instr mk_pexpr_instr(expr const & v) {
    vm_instr r(opcode::Pexpr);
    r.m_expr = new expr(v);
    return r;
}

vm_instr mk_ret_instr() { return vm_instr(opcode::Ret); }

vm_instr mk_destruct_instr() { return vm_instr(opcode::Destruct); }

vm_instr mk_unreachable_instr() { return vm_instr(opcode::Unreachable); }

vm_instr mk_apply_instr() { return vm_instr(opcode::Apply); }

vm_instr mk_nat_cases_instr(unsigned pc1, unsigned pc2) {
    vm_instr r(opcode::NatCases);
    r.m_pc[0] = pc1;
    r.m_pc[1] = pc2;
    return r;
}

vm_instr mk_cases2_instr(unsigned pc1, unsigned pc2) {
    vm_instr r(opcode::Cases2);
    r.m_pc[0] = pc1;
    r.m_pc[1] = pc2;
    return r;
}

vm_instr mk_casesn_instr(unsigned num_pc, unsigned const * pcs) {
    lean_assert(num_pc >= 2);
    vm_instr r(opcode::CasesN);
    r.m_cases_idx = 0; /* not really needed, but it avoids a valgrind warning. */
    r.m_npcs = new unsigned[num_pc + 1];
    r.m_npcs[0] = num_pc;
    for (unsigned i = 0; i < num_pc; i++)
        r.m_npcs[i+1] = pcs[i];
    return r;
}

vm_instr mk_builtin_cases_instr(unsigned cases_idx, unsigned num_pc, unsigned const * pcs) {
    vm_instr r(opcode::BuiltinCases);
    r.m_cases_idx = cases_idx;
    r.m_npcs      = new unsigned[num_pc + 1];
    r.m_npcs[0]   = num_pc;
    for (unsigned i = 0; i < num_pc; i++)
        r.m_npcs[i+1] = pcs[i];
    return r;
}

vm_instr mk_invoke_global_instr(unsigned fn_idx) {
    vm_instr r(opcode::InvokeGlobal);
    r.m_fn_idx = fn_idx;
    return r;
}

vm_instr mk_invoke_builtin_instr(unsigned fn_idx) {
    vm_instr r(opcode::InvokeBuiltin);
    r.m_fn_idx = fn_idx;
    return r;
}

vm_instr mk_invoke_cfun_instr(unsigned fn_idx) {
    vm_instr r(opcode::InvokeCFun);
    r.m_fn_idx = fn_idx;
    return r;
}

vm_instr mk_closure_instr(unsigned fn_idx, unsigned n) {
    vm_instr r(opcode::Closure);
    r.m_fn_idx = fn_idx;
    r.m_nargs  = n;
    return r;
}

void vm_instr::copy_args(vm_instr const & i) {
    switch (i.m_op) {
    case opcode::InvokeGlobal: case opcode::InvokeBuiltin: case opcode::InvokeCFun:
        m_fn_idx = i.m_fn_idx;
        break;
    case opcode::Closure:
        m_fn_idx = i.m_fn_idx;
        m_nargs  = i.m_nargs;
        break;
    case opcode::Push: case opcode::Proj:
        m_idx  = i.m_idx;
        break;
    case opcode::Drop:
        m_num = i.m_num;
        break;
    case opcode::Goto:
        m_pc[0] = i.m_pc[0];
        break;
    case opcode::Cases2: case opcode::NatCases:
        m_pc[0] = i.m_pc[0];
        m_pc[1] = i.m_pc[1];
        break;
    case opcode::CasesN:
    case opcode::BuiltinCases:
        m_npcs = new unsigned[i.m_npcs[0] + 1];
        for (unsigned j = 0; j < i.m_npcs[0] + 1; j++)
            m_npcs[j] = i.m_npcs[j];
        m_cases_idx = i.m_cases_idx;
        break;
    case opcode::SConstructor:
        m_cidx = i.m_cidx;
        break;
    case opcode::Constructor:
        m_cidx    = i.m_cidx;
        m_nfields = i.m_nfields;
        break;
    case opcode::Num:
        m_mpz = new mpz(*i.m_mpz);
        break;
    case opcode::Pexpr:
        m_expr = new expr(*i.m_expr);
        break;
    case opcode::Ret:         case opcode::Destruct:
    case opcode::Unreachable: case opcode::Apply:
        break;
    }
}

vm_instr::vm_instr(vm_instr const & i):
    m_op(i.m_op) {
    copy_args(i);
}

vm_instr::vm_instr(vm_instr && i):
    m_op(i.m_op) {
    switch (m_op) {
    case opcode::Num:
        m_mpz    = i.m_mpz;
        i.m_mpz  = nullptr;
        break;
    case opcode::CasesN: case opcode::BuiltinCases:
        m_npcs      = i.m_npcs;
        m_cases_idx = i.m_cases_idx;
        i.m_npcs    = nullptr;
        break;
    default:
        copy_args(i);
        break;
    }
}

vm_instr::~vm_instr() {
    switch (m_op) {
    case opcode::Num:
        delete m_mpz;
        break;
    case opcode::CasesN: case opcode::BuiltinCases:
        delete[] m_npcs;
        break;
    case opcode::Pexpr:
        delete m_expr;
        break;
    default:
        break;
    }
}

vm_instr & vm_instr::operator=(vm_instr const & s) {
    m_op = s.m_op;
    copy_args(s);
    return *this;
}

vm_instr & vm_instr::operator=(vm_instr && s) {
    m_op = s.m_op;
    switch (m_op) {
    case opcode::Num:
        m_mpz    = s.m_mpz;
        s.m_mpz  = nullptr;
        break;
    case opcode::CasesN: case opcode::BuiltinCases:
        m_cases_idx = s.m_cases_idx;
        m_npcs      = s.m_npcs;
        s.m_npcs    = nullptr;
        break;
    default:
        copy_args(s);
        break;
    }
    return *this;
}

void vm_instr::serialize(serializer & s, std::function<name(unsigned)> const & idx2name) const {
    s << static_cast<char>(m_op);
    switch (m_op) {
    case opcode::InvokeGlobal: case opcode::InvokeBuiltin: case opcode::InvokeCFun:
        s << idx2name(m_fn_idx);
        break;
    case opcode::Closure:
        s << idx2name(m_fn_idx) << m_nargs;
        break;
    case opcode::Push: case opcode::Proj:
        s << m_idx;
        break;
    case opcode::Drop:
        s << m_num;
        break;
    case opcode::Goto:
        s << m_pc[0];
        break;
    case opcode::Cases2: case opcode::NatCases:
        s << m_pc[0];
        s << m_pc[1];
        break;
    case opcode::BuiltinCases:
        s << m_cases_idx;
        // continue on CasesN
    case opcode::CasesN:
        s << m_npcs[0];
        for (unsigned j = 1; j < m_npcs[0] + 1; j++)
            s << m_npcs[j];
        break;
    case opcode::SConstructor:
        s << m_cidx;
        break;
    case opcode::Constructor:
        s << m_cidx << m_nfields;
        break;
    case opcode::Num:
        s << *m_mpz;
        break;
    case opcode::Pexpr:
        s << *m_expr;
        break;
    case opcode::Ret:         case opcode::Destruct:
    case opcode::Unreachable: case opcode::Apply:
        break;
    }
}

static unsigned read_fn_idx(deserializer & d, name_map<unsigned> const & name2idx) {
    name n;
    d >> n;
    if (auto r = name2idx.find(n))
        return *r;
    else
        throw corrupted_stream_exception();
}

static void read_cases_pcs(deserializer & d, buffer<unsigned> & pcs) {
    unsigned n = d.read_unsigned();
    for (unsigned j = 0; j < n; j++)
        pcs.push_back(d.read_unsigned());
}

static vm_instr read_vm_instr(deserializer & d, name_map<unsigned> const & name2idx) {
    opcode op = static_cast<opcode>(d.read_char());
    unsigned pc, idx;
    switch (op) {
    case opcode::InvokeGlobal:
        return mk_invoke_global_instr(read_fn_idx(d, name2idx));
    case opcode::InvokeBuiltin:
        return mk_invoke_builtin_instr(read_fn_idx(d, name2idx));
    case opcode::InvokeCFun:
        return mk_invoke_cfun_instr(read_fn_idx(d, name2idx));
    case opcode::Closure:
        idx = read_fn_idx(d, name2idx);
        return mk_closure_instr(idx, d.read_unsigned());
    case opcode::Push:
        return mk_push_instr(d.read_unsigned());
    case opcode::Proj:
        return mk_proj_instr(d.read_unsigned());
    case opcode::Drop:
        return mk_drop_instr(d.read_unsigned());
    case opcode::Goto:
        return mk_goto_instr(d.read_unsigned());
    case opcode::Cases2:
        pc = d.read_unsigned();
        return mk_cases2_instr(pc, d.read_unsigned());
    case opcode::NatCases:
        pc = d.read_unsigned();
        return mk_nat_cases_instr(pc, d.read_unsigned());
    case opcode::CasesN: {
        buffer<unsigned> pcs;
        read_cases_pcs(d, pcs);
        return mk_casesn_instr(pcs.size(), pcs.data());
    }
    case opcode::BuiltinCases: {
        idx = d.read_unsigned();
        buffer<unsigned> pcs;
        read_cases_pcs(d, pcs);
        return mk_builtin_cases_instr(idx, pcs.size(), pcs.data());
    }
    case opcode::SConstructor:
        return mk_sconstructor_instr(d.read_unsigned());
    case opcode::Constructor:
        idx = d.read_unsigned();
        return mk_constructor_instr(idx, d.read_unsigned());
    case opcode::Num:
        return mk_num_instr(read_mpz(d));
    case opcode::Pexpr:
        return mk_pexpr_instr(read_expr(d));
    case opcode::Ret:
        return mk_ret_instr();
    case opcode::Destruct:
        return mk_destruct_instr();
    case opcode::Unreachable:
        return mk_unreachable_instr();
    case opcode::Apply:
        return mk_apply_instr();
    }
    lean_unreachable();
}

vm_decl_cell::vm_decl_cell(name const & n, unsigned idx, unsigned arity, vm_function fn):
    m_rc(0), m_kind(vm_decl_kind::Builtin), m_name(n), m_idx(idx), m_arity(arity), m_fn(fn) {}

vm_decl_cell::vm_decl_cell(name const & n, unsigned idx, unsigned arity, vm_cfunction fn):
    m_rc(0), m_kind(vm_decl_kind::CFun), m_name(n), m_idx(idx), m_arity(arity), m_cfn(fn) {}

vm_decl_cell::vm_decl_cell(name const & n, unsigned idx, expr const & e, unsigned code_sz, vm_instr const * code):
    m_rc(0), m_kind(vm_decl_kind::Bytecode), m_name(n), m_idx(idx), m_expr(e), m_arity(0),
    m_code_size(code_sz) {
    expr it = e;
    while (is_lambda(it)) {
        m_arity++;
        it = binding_body(it);
    }
    m_code = new vm_instr[code_sz];
    for (unsigned i = 0; i < code_sz; i++)
        m_code[i] = code[i];
}

vm_decl_cell::~vm_decl_cell() {
    if (m_kind == vm_decl_kind::Bytecode)
        delete[] m_code;
}

void vm_decl_cell::dealloc() {
    delete this;
}

/** \brief VM builtin functions */
static name_map<std::tuple<unsigned, char const *, vm_function>> * g_vm_builtins = nullptr;
static name_map<std::tuple<unsigned, char const *, vm_cfunction>> * g_vm_cbuiltins = nullptr;
static name_map<std::tuple<char const *, vm_cases_function>> * g_vm_cases_builtins = nullptr;
static bool g_may_update_vm_builtins = true;

void declare_vm_builtin(name const & n, char const * i, unsigned arity, vm_function fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_builtins->insert(n, std::make_tuple(arity, i, fn));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_0 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(0, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_1 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(1, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_2 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(2, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_3 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(3, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_4 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(4, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_5 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(5, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_6 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(6, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_7 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(7, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, vm_cfunction_8 fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(8, i, reinterpret_cast<vm_cfunction>(fn)));
}

void declare_vm_builtin(name const & n, char const * i, unsigned arity, vm_cfunction_N fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cbuiltins->insert(n, std::make_tuple(arity, i, reinterpret_cast<vm_cfunction>(fn)));
}

bool is_vm_builtin_function(name const & fn) {
    return g_vm_builtins->contains(fn) || g_vm_cbuiltins->contains(fn) || g_vm_cases_builtins->contains(fn);
}

void declare_vm_cases_builtin(name const & n, char const * i, vm_cases_function fn) {
    lean_assert(g_may_update_vm_builtins);
    g_vm_cases_builtins->insert(n, std::make_tuple(i, fn));
}

/** \brief VM function/constant declarations are stored in an environment extension. */
struct vm_decls : public environment_extension {
    name_map<unsigned>        m_name2idx;
    unsigned_map<vm_decl>     m_decls;
    unsigned                  m_next_decl_idx{0};

    name_map<unsigned>              m_cases2idx;
    unsigned_map<vm_cases_function> m_cases;
    unsigned_map<name>              m_cases_names;
    unsigned                        m_next_cases_idx{0};

    vm_decls() {
        g_vm_builtins->for_each([&](name const & n, std::tuple<unsigned, char const *, vm_function> const & p) {
                add(vm_decl(n, m_next_decl_idx, std::get<0>(p), std::get<2>(p)));
                m_next_decl_idx++;
            });
        g_vm_cbuiltins->for_each([&](name const & n, std::tuple<unsigned, char const *, vm_cfunction> const & p) {
                add(vm_decl(n, m_next_decl_idx, std::get<0>(p), std::get<2>(p)));
                m_next_decl_idx++;
            });
        g_vm_cases_builtins->for_each([&](name const & n, std::tuple<char const *, vm_cases_function> const & p) {
                unsigned idx = m_next_cases_idx;
                m_cases2idx.insert(n, idx);
                m_cases.insert(idx, std::get<1>(p));
                m_cases_names.insert(idx, n);
                m_next_cases_idx++;
            });
    }

    void add(vm_decl const & d) {
        if (m_name2idx.contains(d.get_name()))
            throw exception(sstream() << "VM already contains code for '" << d.get_name() << "'");
        m_name2idx.insert(d.get_name(), d.get_idx());
        m_decls.insert(d.get_idx(), d);
    }

    unsigned reserve(name const & n, expr const & e) {
        if (m_name2idx.contains(n))
            throw exception(sstream() << "VM already contains code for '" << n << "'");
        unsigned idx = m_next_decl_idx;
        m_next_decl_idx++;
        m_name2idx.insert(n, idx);
        m_decls.insert(idx, vm_decl(n, idx, e, 0, nullptr));
        return idx;
    }

    void update(name const & n, unsigned code_sz, vm_instr const * code) {
        lean_assert(m_name2idx.contains(n));
        unsigned idx      = *m_name2idx.find(n);
        vm_decl const * d = m_decls.find(idx);
        m_decls.insert(idx, vm_decl(n, idx, d->get_expr(), code_sz, code));
    }
};

struct vm_decls_reg {
    std::shared_ptr<vm_decls> m_init_decls;
    unsigned                  m_ext_id;
    vm_decls_reg() {
        m_init_decls = std::make_shared<vm_decls>();
        m_ext_id     = environment::register_extension(m_init_decls);
    }
};

static vm_decls_reg * g_ext = nullptr;
static vm_decls const & get_extension(environment const & env) {
    return static_cast<vm_decls const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, vm_decls const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<vm_decls>(ext));
}

static environment add_native(environment const & env, name const & n, unsigned arity, vm_cfunction fn) {
    auto ext = get_extension(env);
    if (auto idx = ext.m_name2idx.find(n)) {
        lean_assert(ext.m_decls.find(*idx)->get_arity() == arity);
        ext.m_decls.insert(*idx, vm_decl(n, *idx, arity, fn));
    } else {
        ext.add(vm_decl(n, ext.m_decls.size(), arity, fn));
    }
    return update(env, ext);
}

environment add_native(environment const & env, name const & n, vm_cfunction_0 fn) {
    return add_native(env, n, 0, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_1 fn) {
    return add_native(env, n, 1, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_2 fn) {
    return add_native(env, n, 2, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_3 fn) {
    return add_native(env, n, 3, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_4 fn) {
    return add_native(env, n, 4, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_5 fn) {
    return add_native(env, n, 5, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_6 fn) {
    return add_native(env, n, 6, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_7 fn) {
    return add_native(env, n, 7, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, vm_cfunction_8 fn) {
    return add_native(env, n, 8, reinterpret_cast<vm_cfunction>(fn));
}

environment add_native(environment const & env, name const & n, unsigned arity, vm_cfunction_N fn) {
    return add_native(env, n, arity, reinterpret_cast<vm_cfunction>(fn));
}

bool is_vm_function(environment const & env, name const & fn) {
    auto const & ext = get_extension(env);
    return ext.m_name2idx.contains(fn) || g_vm_builtins->contains(fn);
}

optional<unsigned> get_vm_constant_idx(environment const & env, name const & n) {
    auto const & ext = get_extension(env);
    if (auto r = ext.m_name2idx.find(n))
        return optional<unsigned>(*r);
    else
        return optional<unsigned>();
}

optional<unsigned> get_vm_builtin_idx(name const & n) {
    lean_assert(g_ext);
    if (auto r = g_ext->m_init_decls->m_name2idx.find(n))
        return optional<unsigned>(*r);
    else
        return optional<unsigned>();
}

static std::string * g_vm_reserve_key = nullptr;
static std::string * g_vm_code_key = nullptr;

environment reserve_vm_index(environment const & env, name const & fn, expr const & e) {
    vm_decls ext = get_extension(env);
    ext.reserve(fn, e);
    environment new_env = update(env, ext);
    return module::add(new_env, *g_vm_reserve_key, [=](environment const &, serializer & s) {
            s << fn << e;
        });
}

static void reserve_reader(deserializer & d, shared_environment & senv,
                           std::function<void(asynch_update_fn const &)> &,
                           std::function<void(delayed_update_fn const &)> &) {
    name fn; expr e;
    d >> fn >> e;
    senv.update([&](environment const & env) -> environment {
            vm_decls ext = get_extension(env);
            ext.reserve(fn, e);
            return update(env, ext);
        });
}

void serialize_code(serializer & s, unsigned fidx, unsigned_map<vm_decl> const & decls) {
    vm_decl const * d = decls.find(fidx);
    s << d->get_name() << d->get_code_size();
    vm_instr const * code = d->get_code();
    auto fn = [&](unsigned idx) { return decls.find(idx)->get_name(); };
    for (unsigned i = 0; i < d->get_code_size(); i++) {
        code[i].serialize(s, fn);
    }
}

static void code_reader(deserializer & d, shared_environment & senv,
                        std::function<void(asynch_update_fn const &)> &,
                        std::function<void(delayed_update_fn const &)> &) {
    senv.update([&](environment const & env) -> environment {
            name fn; unsigned code_sz;
            d >> fn;
            d >> code_sz;
            vm_decls ext = get_extension(env);
            buffer<vm_instr> code;
            for (unsigned i = 0; i < code_sz; i++) {
                code.push_back(read_vm_instr(d, ext.m_name2idx));
            }
            ext.update(fn, code_sz, code.data());
            return update(env, ext);
        });
}

environment update_vm_code(environment const & env, name const & fn, unsigned code_sz, vm_instr const * code) {
    vm_decls ext = get_extension(env);
    ext.update(fn, code_sz, code);
    environment new_env = update(env, ext);
    unsigned fidx       = *ext.m_name2idx.find(fn);
    return module::add(new_env, *g_vm_code_key, [=](environment const & env, serializer & s) {
            serialize_code(s, fidx, get_extension(env).m_decls);
        });
}

environment add_vm_code(environment const & env, name const & fn, expr const & e, unsigned code_sz, vm_instr const * code) {
    environment new_env = reserve_vm_index(env, fn, e);
    return update_vm_code(new_env, fn, code_sz, code);
}

optional<vm_decl> get_vm_decl(environment const & env, name const & n) {
    vm_decls const & ext = get_extension(env);
    if (auto idx = ext.m_name2idx.find(n))
        return optional<vm_decl>(*ext.m_decls.find(*idx));
    else
        return optional<vm_decl>();
}

optional<unsigned> get_vm_builtin_cases_idx(environment const & env, name const & n) {
    vm_decls const & ext = get_extension(env);
    if (auto idx = ext.m_cases2idx.find(n))
        return optional<unsigned>(*idx);
    else
        return optional<unsigned>();
}

vm_state::vm_state(environment const & env):
    m_env(env),
    m_decl_map(get_extension(m_env).m_decls),
    m_decl_vector(get_extension(m_env).m_next_decl_idx),
    m_builtin_cases_map(get_extension(m_env).m_cases),
    m_builtin_cases_vector(get_extension(m_env).m_next_cases_idx),
    m_builtin_cases_names(get_extension(m_env).m_cases_names),
    m_fn_name2idx(get_extension(m_env).m_name2idx),
    m_code(nullptr),
    m_fn_idx(0),
    m_bp(0) {
}

void vm_state::update_env(environment const & env) {
    lean_assert(env.is_descendant(env));
    m_env         = env;
    auto ext      = get_extension(env);
    m_decl_map    = ext.m_decls;
    lean_assert(ext.m_next_decl_idx >= m_decl_vector.size());
    m_decl_vector.resize(ext.m_next_decl_idx);
    m_fn_name2idx = ext.m_name2idx;
    lean_assert(is_eqp(m_builtin_cases_map, ext.m_cases));
}

void vm_state::push_fields(vm_obj const & obj) {
    if (is_constructor(obj)) {
        unsigned nflds = csize(obj);
        vm_obj const * flds = cfields(obj);
        for (unsigned i = 0; i < nflds; i++, flds++) {
            m_stack.push_back(*flds);
        }
    }
}

void vm_state::invoke_builtin(vm_decl const & d) {
    unsigned saved_bp = m_bp;
    unsigned sz = m_stack.size();
    m_bp = sz;
    d.get_fn()(*this);
    lean_assert(m_stack.size() == sz + 1);
    m_bp = saved_bp;
    sz = m_stack.size();
    swap(m_stack[sz - d.get_arity() - 1], m_stack[sz - 1]);
    m_stack.resize(sz - d.get_arity());
    m_pc++;
}

LEAN_THREAD_VALUE(vm_state *, g_vm_state, nullptr);

scope_vm_state::scope_vm_state(vm_state & s):
    m_prev(g_vm_state) {
    g_vm_state = &s;
}

scope_vm_state::~scope_vm_state() {
    g_vm_state = m_prev;
}

void vm_state::invoke_cfun(vm_decl const & d) {
    flet<vm_state *> Set(g_vm_state, this);
    auto & S       = m_stack;
    unsigned sz    = S.size();
    unsigned arity = d.get_arity();
    vm_obj r;
    /* Important The stack m_stack may be resized during the execution of the function d.get_cfn().
       Thus, to make sure the arguments are not garbage collected, we copy them into local variables a1 ... an.
       The copy operation will bump the reference counter. */
    switch (arity) {
    case 0:
        r = reinterpret_cast<vm_cfunction_0>(d.get_cfn())();
        break;
    case 1: {
        vm_obj a1 = S[sz-1];
        r = reinterpret_cast<vm_cfunction_1>(d.get_cfn())(a1);
        break;
    }
    case 2: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2];
        r = reinterpret_cast<vm_cfunction_2>(d.get_cfn())(a1, a2);
        break;
    }
    case 3: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3];
        r = reinterpret_cast<vm_cfunction_3>(d.get_cfn())(a1, a2, a3);
        break;
    }
    case 4: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4];
        r = reinterpret_cast<vm_cfunction_4>(d.get_cfn())(a1, a2, a3, a4);
        break;
    }
    case 5: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4], a5 = S[sz - 5];
        r = reinterpret_cast<vm_cfunction_5>(d.get_cfn())(a1, a2, a3, a4, a5);
        break;
    }
    case 6: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4], a5 = S[sz - 5], a6 = S[sz - 6];
        r = reinterpret_cast<vm_cfunction_6>(d.get_cfn())(a1, a2, a3, a4, a5, a6);
        break;
    }
    case 7: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4], a5 = S[sz - 5], a6 = S[sz - 6];
        vm_obj a7 = S[sz - 7];
        r = reinterpret_cast<vm_cfunction_7>(d.get_cfn())(a1, a2, a3, a4, a5, a6, a7);
        break;
    }
    case 8: {
        vm_obj a1 = S[sz - 1], a2 = S[sz - 2], a3 = S[sz - 3], a4 = S[sz - 4], a5 = S[sz - 5], a6 = S[sz - 6];
        vm_obj a7 = S[sz - 7], a8 = S[sz - 8];
        r = reinterpret_cast<vm_cfunction_8>(d.get_cfn())(a1, a2, a3, a4, a5, a6, a7, a8);
        break;
    }
    default: {
        buffer<vm_obj> args;
        unsigned i = sz;
        while (i > sz - arity) {
            --i;
            args.push_back(m_stack[i]);
        }
        lean_assert(args.size() == arity);
        r = reinterpret_cast<vm_cfunction_N>(d.get_cfn())(args.size(), args.data());
        break;
    }}
    m_stack.resize(sz - arity);
    m_stack.push_back(r);
    m_pc++;
}

inline vm_cfunction_1 to_fn1(vm_decl const & d) { return reinterpret_cast<vm_cfunction_1>(d.get_cfn()); }
inline vm_cfunction_2 to_fn2(vm_decl const & d) { return reinterpret_cast<vm_cfunction_2>(d.get_cfn()); }
inline vm_cfunction_3 to_fn3(vm_decl const & d) { return reinterpret_cast<vm_cfunction_3>(d.get_cfn()); }
inline vm_cfunction_4 to_fn4(vm_decl const & d) { return reinterpret_cast<vm_cfunction_4>(d.get_cfn()); }
inline vm_cfunction_5 to_fn5(vm_decl const & d) { return reinterpret_cast<vm_cfunction_5>(d.get_cfn()); }
inline vm_cfunction_6 to_fn6(vm_decl const & d) { return reinterpret_cast<vm_cfunction_6>(d.get_cfn()); }
inline vm_cfunction_7 to_fn7(vm_decl const & d) { return reinterpret_cast<vm_cfunction_7>(d.get_cfn()); }
inline vm_cfunction_8 to_fn8(vm_decl const & d) { return reinterpret_cast<vm_cfunction_8>(d.get_cfn()); }
inline vm_cfunction_N to_fnN(vm_decl const & d) { return reinterpret_cast<vm_cfunction_N>(d.get_cfn()); }

vm_obj vm_state::invoke_closure(vm_obj const & fn, unsigned DEBUG_CODE(nargs)) {
    unsigned saved_pc = m_pc;
    unsigned fn_idx   = cfn_idx(fn);
    vm_decl d         = get_decl(fn_idx);
    unsigned csz      = csize(fn);
    std::copy(cfields(fn), cfields(fn) + csz, std::back_inserter(m_stack));
    lean_assert(nargs + csz == d.get_arity());
    switch (d.kind()) {
    case vm_decl_kind::Bytecode:
        invoke_global(d);
        run();
        break;
    case vm_decl_kind::Builtin:
        invoke_builtin(d);
        break;
    case vm_decl_kind::CFun:
        invoke_cfun(d);
        break;
    }
    m_pc     = saved_pc;
    vm_obj r = m_stack.back();
    m_stack.pop_back();
    return r;
}

static void to_cbuffer(vm_obj const & fn, buffer<vm_obj> & args) {
    vm_obj const * begin = cfields(fn);
    vm_obj const * end   = begin + csize(fn);
    vm_obj const * it    = end;
    while (it != begin) {
        --it;
        args.push_back(*it);
    }
}

vm_obj vm_state::invoke(unsigned fn_idx, unsigned nargs, vm_obj const * as) {
    vm_decl d = get_decl(fn_idx);
    lean_assert(d.get_arity() <= nargs);
    std::copy(as, as + nargs, std::back_inserter(m_stack));
    invoke_fn(fn_idx);
    if (d.get_arity() < nargs)
        apply(nargs - d.get_arity());
    vm_obj r = m_stack.back();
    m_stack.pop_back();
    return r;
}

vm_obj vm_state::invoke(name const & fn, unsigned nargs, vm_obj const * as) {
    if (auto r = m_fn_name2idx.find(fn)) {
        return invoke(*r, nargs, as);
    } else {
        throw exception(sstream() << "VM does not have code for '" << fn << "'");
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 1;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: lean_unreachable();
            case 1: return to_fn1(d)(a1);
            case 2: return to_fn2(d)(cfield(fn, 0), a1);
            case 3: return to_fn3(d)(cfield(fn, 1), cfield(fn, 0), a1);
            case 4: return to_fn4(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            case 5: return to_fn5(d)(cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            case 6: return to_fn6(d)(cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            case 7: return to_fn7(d)(cfield(fn, 5), cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            case 8: return to_fn8(d)(cfield(fn, 6), cfield(fn, 5), cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a1);
            return invoke_closure(fn, 1);
        }
    } else {
        lean_unreachable();
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 2;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: lean_unreachable();
            case 2: return to_fn2(d)(a1, a2);
            case 3: return to_fn3(d)(cfield(fn, 0), a1, a2);
            case 4: return to_fn4(d)(cfield(fn, 1), cfield(fn, 0), a1, a2);
            case 5: return to_fn5(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2);
            case 6: return to_fn6(d)(cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2);
            case 7: return to_fn7(d)(cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2);
            case 8: return to_fn8(d)(cfield(fn, 5), cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 2);
        }
    } else {
        lean_assert(nargs > d.get_arity());
        return invoke(invoke(fn, a1), a2);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 3;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: lean_unreachable();
            case 3: return to_fn3(d)(a1, a2, a3);
            case 4: return to_fn4(d)(cfield(fn, 0), a1, a2, a3);
            case 5: return to_fn5(d)(cfield(fn, 1), cfield(fn, 0), a1, a2, a3);
            case 6: return to_fn6(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3);
            case 7: return to_fn7(d)(cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3);
            case 8: return to_fn8(d)(cfield(fn, 4), cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 3);
        }
    } else if (nargs == d.get_arity() + 1) {
        return invoke(invoke(fn, a1, a2), a3);
    } else {
        return invoke(invoke(fn, a1), a2, a3);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 4;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: lean_unreachable();
            case 4: return to_fn4(d)(a1, a2, a3, a4);
            case 5: return to_fn5(d)(cfield(fn, 0), a1, a2, a3, a4);
            case 6: return to_fn6(d)(cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4);
            case 7: return to_fn7(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4);
            case 8: return to_fn8(d)(cfield(fn, 3), cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 4);
        }
    } else if (nargs == d.get_arity() + 1) {
        return invoke(invoke(fn, a1, a2, a3), a4);
    } else if (nargs == d.get_arity() + 2) {
        return invoke(invoke(fn, a1, a2), a3, a4);
    } else {
        return invoke(invoke(fn, a1), a2, a3, a4);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                        vm_obj const & a5) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 5;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a5);
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: case 4: lean_unreachable();
            case 5: return to_fn5(d)(a1, a2, a3, a4, a5);
            case 6: return to_fn6(d)(cfield(fn, 0), a1, a2, a3, a4, a5);
            case 7: return to_fn7(d)(cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4, a5);
            case 8: return to_fn8(d)(cfield(fn, 2), cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4, a5);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                args.push_back(a5);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a5);
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 5);
        }
    } else if (nargs == d.get_arity() + 1) {
        return invoke(invoke(fn, a1, a2, a3, a4), a5);
    } else if (nargs == d.get_arity() + 2) {
        return invoke(invoke(fn, a1, a2, a3), a4, a5);
    } else if (nargs == d.get_arity() + 3) {
        return invoke(invoke(fn, a1, a2), a3, a4, a5);
    } else {
        return invoke(invoke(fn, a1), a2, a3, a4, a5);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                        vm_obj const & a5, vm_obj const & a6) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 6;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a6);
        args.push_back(a5);
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: case 4: case 5: lean_unreachable();
            case 6: return to_fn6(d)(a1, a2, a3, a4, a5, a6);
            case 7: return to_fn7(d)(cfield(fn, 0), a1, a2, a3, a4, a5, a6);
            case 8: return to_fn8(d)(cfield(fn, 1), cfield(fn, 0), a1, a2, a3, a4, a5, a6);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                args.push_back(a5);
                args.push_back(a6);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a6);
            m_stack.push_back(a5);
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 6);
        }
    } else if (nargs == d.get_arity() + 1) {
        return invoke(invoke(fn, a1, a2, a3, a4, a5), a6);
    } else if (nargs == d.get_arity() + 2) {
        return invoke(invoke(fn, a1, a2, a3, a4), a5, a6);
    } else if (nargs == d.get_arity() + 3) {
        return invoke(invoke(fn, a1, a2, a3), a4, a5, a6);
    } else if (nargs == d.get_arity() + 4) {
        return invoke(invoke(fn, a1, a2), a3, a4, a5, a6);
    } else {
        return invoke(invoke(fn, a1), a2, a3, a4, a5, a6);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                        vm_obj const & a5, vm_obj const & a6, vm_obj const & a7) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 7;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a7);
        args.push_back(a6);
        args.push_back(a5);
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: case 4: case 5: case 6: lean_unreachable();
            case 7: return to_fn7(d)(a1, a2, a3, a4, a5, a6, a7);
            case 8: return to_fn8(d)(cfield(fn, 0), a1, a2, a3, a4, a5, a6, a7);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                args.push_back(a5);
                args.push_back(a6);
                args.push_back(a7);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a7);
            m_stack.push_back(a6);
            m_stack.push_back(a5);
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 7);
        }
    } else if (nargs == d.get_arity() + 1) {
        return invoke(invoke(fn, a1, a2, a3, a4, a5, a6), a7);
    } else if (nargs == d.get_arity() + 2) {
        return invoke(invoke(fn, a1, a2, a3, a4, a5), a6, a7);
    } else if (nargs == d.get_arity() + 3) {
        return invoke(invoke(fn, a1, a2, a3, a4), a5, a6, a7);
    } else if (nargs == d.get_arity() + 4) {
        return invoke(invoke(fn, a1, a2, a3), a4, a5, a6, a7);
    } else if (nargs == d.get_arity() + 5) {
        return invoke(invoke(fn, a1, a2), a3, a4, a5, a6, a7);
    } else {
        return invoke(invoke(fn, a1), a2, a3, a4, a5, a6, a7);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
                        vm_obj const & a5, vm_obj const & a6, vm_obj const & a7, vm_obj const & a8) {
    unsigned fn_idx = cfn_idx(fn);
    vm_decl d       = get_decl(fn_idx);
    unsigned nargs  = csize(fn) + 8;
    if (nargs < d.get_arity()) {
        buffer<vm_obj> args;
        args.push_back(a8);
        args.push_back(a7);
        args.push_back(a6);
        args.push_back(a5);
        args.push_back(a4);
        args.push_back(a3);
        args.push_back(a2);
        args.push_back(a1);
        args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, args.size(), args.data());
    } else if (nargs == d.get_arity()) {
        if (d.is_cfun()) {
            switch (d.get_arity()) {
            case 0: case 1: case 2: case 3: case 4: case 5: case 6: case 7: lean_unreachable();
            case 8: return to_fn8(d)(a1, a2, a3, a4, a5, a6, a7, a8);
            default:
                buffer<vm_obj> args;
                to_cbuffer(fn, args);
                args.push_back(a1);
                args.push_back(a2);
                args.push_back(a3);
                args.push_back(a4);
                args.push_back(a5);
                args.push_back(a6);
                args.push_back(a7);
                args.push_back(a8);
                return to_fnN(d)(args.size(), args.data());
            }
        } else {
            m_stack.push_back(a8);
            m_stack.push_back(a7);
            m_stack.push_back(a6);
            m_stack.push_back(a5);
            m_stack.push_back(a4);
            m_stack.push_back(a3);
            m_stack.push_back(a2);
            m_stack.push_back(a1);
            return invoke_closure(fn, 8);
        }
    } else if (nargs == d.get_arity() + 1) {
        return invoke(invoke(fn, a1, a2, a3, a4, a5, a6, a7), a8);
    } else if (nargs == d.get_arity() + 2) {
        return invoke(invoke(fn, a1, a2, a3, a4, a5, a6), a7, a8);
    } else if (nargs == d.get_arity() + 3) {
        return invoke(invoke(fn, a1, a2, a3, a4, a5), a6, a7, a8);
    } else if (nargs == d.get_arity() + 4) {
        return invoke(invoke(fn, a1, a2, a3, a4), a5, a6, a7, a8);
    } else if (nargs == d.get_arity() + 5) {
        return invoke(invoke(fn, a1, a2, a3), a4, a5, a6, a7, a8);
    } else if (nargs == d.get_arity() + 6) {
        return invoke(invoke(fn, a1, a2), a3, a4, a5, a6, a7, a8);
    } else {
        return invoke(invoke(fn, a1), a2, a3, a4, a5, a6, a7, a8);
    }
}

vm_obj vm_state::invoke(vm_obj const & fn, unsigned nargs, vm_obj const * args) {
    if (nargs <= 8) {
        switch (nargs) {
        case 1: return invoke(fn, args[0]);
        case 2: return invoke(fn, args[0], args[1]);
        case 3: return invoke(fn, args[0], args[1], args[2]);
        case 4: return invoke(fn, args[0], args[1], args[2], args[3]);
        case 5: return invoke(fn, args[0], args[1], args[2], args[3], args[4]);
        case 6: return invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5]);
        case 7: return invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
        case 8: return invoke(fn, args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
        default: lean_unreachable();
        }
    }
    unsigned fn_idx    = cfn_idx(fn);
    vm_decl d          = get_decl(fn_idx);
    unsigned new_nargs = csize(fn) + nargs;
    if (new_nargs < d.get_arity()) {
        buffer<vm_obj> new_args;
        unsigned i = nargs;
        while (i > 0) { --i; new_args.push_back(args[i]); }
        new_args.append(csize(fn), cfields(fn));
        return mk_vm_closure(fn_idx, new_args.size(), new_args.data());
    } else if (new_nargs == d.get_arity()) {
        if (d.is_cfun()) {
            if (csize(fn) == 0) {
                return to_fnN(d)(nargs, args);
            } else {
                buffer<vm_obj> new_args;
                to_cbuffer(fn, new_args);
                new_args.append(nargs, args);
                return to_fnN(d)(nargs, args);
            }
        } else {
            unsigned i = nargs;
            while (i > 0) { --i; m_stack.push_back(args[i]); }
            return invoke_closure(fn, nargs);
        }
    } else {
        lean_assert(nargs + csize(fn) > d.get_arity());
        buffer<vm_obj> new_args;
        buffer<vm_obj> rest_args;
        /* copy arity - csize(fn) arguments to new_args, and the rest to rest_args */
        lean_assert(csize(fn) < d.get_arity());
        unsigned n = d.get_arity() - csize(fn);
        lean_assert(n > 1);
        lean_assert(n < nargs);
        new_args.append(n, args);
        rest_args.append(nargs - n, args + n);
        return invoke(invoke(fn, new_args.size(), new_args.data()), rest_args.size(), rest_args.data());
    }
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, a1);
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, a1, a2);
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, a1, a2, a3);
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, a1, a2, a3, a4);
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, a1, a2, a3, a4, a5);
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, a1, a2, a3, a4, a5, a6);
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6, vm_obj const & a7) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, a1, a2, a3, a4, a5, a6, a7);
}

vm_obj invoke(vm_obj const & fn, vm_obj const & a1, vm_obj const & a2, vm_obj const & a3, vm_obj const & a4,
              vm_obj const & a5, vm_obj const & a6, vm_obj const & a7, vm_obj const & a8) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, a1, a2, a3, a4, a5, a6, a7, a8);
}

vm_obj invoke(vm_obj const & fn, unsigned nargs, vm_obj const * args) {
    lean_assert(g_vm_state);
    return g_vm_state->invoke(fn, nargs, args);
}

vm_obj invoke(unsigned fn_idx, unsigned nargs, vm_obj const * args) {
    lean_assert(g_vm_state);
    vm_obj fn = mk_vm_closure(fn_idx, 0, nullptr);
    return invoke(fn, nargs, args);
}

vm_obj invoke(unsigned fn_idx, vm_obj const & arg) {
    return invoke(fn_idx, 1, &arg);
}

vm_state & get_vm_state() {
    lean_assert(g_vm_state);
    return *g_vm_state;
}

void vm_state::invoke_global(vm_decl const & d) {
    m_call_stack.emplace_back(m_code, m_fn_idx, d.get_arity(), m_pc+1, m_bp);
    m_code            = d.get_code();
    m_fn_idx          = d.get_idx();
    m_pc              = 0;
    m_bp              = m_stack.size() - d.get_arity();
}

void vm_state::invoke(vm_decl const & d) {
    switch (d.kind()) {
    case vm_decl_kind::Bytecode:
        invoke_global(d); break;
    case vm_decl_kind::Builtin:
        invoke_builtin(d); break;
    case vm_decl_kind::CFun:
        invoke_cfun(d); break;
    }
}

void vm_state::display_stack(std::ostream & out) const {
    for (unsigned i = 0; i < m_stack.size(); i++) {
        if (i == m_bp)
            out << "[bp] ";
        else
            out << "     ";
        display(out, m_stack[i]);
        out << "\n";
    }
    if (m_bp == m_stack.size())
        out << "[bp]\n";
}

void vm_state::display_call_stack(std::ostream & out) const {
    for (frame const & fr : m_call_stack) {
        out << ">> (fn_idx := " << fr.m_fn_idx << ", num := " << fr.m_num << ", pc := " << fr.m_pc << ", bp: " << fr.m_bp << ")\n";
    }
}

void vm_state::display_registers(std::ostream & out) const {
    out << "pc: " << m_pc << ", bp: " << m_bp << "\n";
}

void vm_state::run() {
    lean_assert(m_code);
    unsigned init_call_stack_sz = m_call_stack.size();
    m_pc = 0;
    while (true) {
      main_loop:
        vm_instr const & instr = m_code[m_pc];
        DEBUG_CODE({
                /* We only trace VM in debug mode */
                lean_trace(name({"vm", "run"}),
                           tout() << m_pc << ": ";
                           instr.display(tout().get_stream(),
                                         [&](unsigned idx) {
                                             return optional<name>(get_decl(idx).get_name());
                                         },
                                         [&](unsigned idx) {
                                             return optional<name>(*m_builtin_cases_names.find(idx));
                                         });
                           tout() << "\n";
                           display_stack(tout().get_stream());
                           tout() << "\n";)
                    });
        switch (instr.op()) {
        case opcode::Push:
            /* Instruction: push i

               stack before,      after
               ...                ...
               bp :  a_0          bp :  a_0
               ...                ...
               a_i  ==>           a_i
               ...                ...
               v                  v
               a_i
            */
            m_stack.push_back(m_stack[m_bp + instr.get_idx()]);
            m_pc++;
            goto main_loop;
        case opcode::Drop: {
            /* Instruction: drop n

               stack before,      after
               ...                ...
               w                  w
               a_1   ==>          v
               ...
               a_n
               v
            */
            unsigned num = instr.get_num();
            unsigned sz  = m_stack.size();
            lean_assert(sz > num);
            swap(m_stack[sz - num - 1], m_stack[sz - 1]);
            m_stack.resize(sz - num);
            m_pc++;
            goto main_loop;
        }
        case opcode::Goto:
            /* Instruction: goto pc

               m_pc := pc
            */
            m_pc = instr.get_goto_pc();
            goto main_loop;
        case opcode::SConstructor:
            /** Instruction: scnstr i

                stack before,      after
                ...                ...
                v    ==>           v
                #i
            */
            m_stack.push_back(mk_vm_simple(instr.get_cidx()));
            m_pc++;
            goto main_loop;
        case opcode::Constructor: {
            /** Instruction: cnstr i n

                stack before,      after
                ...                ...
                v      ==>         v
                a_1                (#i a_1 ... a_n)
                ...
                a_n
            */
            unsigned nfields = instr.get_nfields();
            unsigned sz      = m_stack.size();
            vm_obj new_value = mk_vm_constructor(instr.get_cidx(), nfields, m_stack.data() + sz - nfields);
            m_stack.resize(sz - nfields + 1);
            swap(m_stack.back(), new_value);
            m_pc++;
            goto main_loop;
        }
        case opcode::Closure: {
            /** Instruction: closure fn n

                stack before,      after
                ...                ...
                v      ==>         v
                a_n                (fn a_n ... a_1)
                ...
                a_1
            */
            unsigned nargs     = instr.get_nargs();
            unsigned sz        = m_stack.size();
            vm_obj new_value   = mk_vm_closure(instr.get_fn_idx(), nargs, m_stack.data() + sz - nargs);
            m_stack.resize(sz - nargs + 1);
            swap(m_stack.back(), new_value);
            m_pc++;
            goto main_loop;
        }
        case opcode::Num:
            /** Instruction: num n

                stack before,      after
                ...                ...
                v    ==>           v
                                   n
            */
            m_stack.push_back(mk_vm_mpz(instr.get_mpz()));
            m_pc++;
            goto main_loop;
        case opcode::Pexpr:
            /** Instruction: pexpr e

                stack before,      after
                ...                ...
                v    ==>           v
                                   e
            */
            m_stack.push_back(to_obj(instr.get_expr()));
            m_pc++;
            goto main_loop;
        case opcode::Destruct: {
            /** Instruction: destruct

                stack before,              after
                ...                        ...
                v                 ==>      v
                (#i a_1 ... a_n)           a_1
                ...
                a_n
            */
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            push_fields(top);
            m_pc++;
            goto main_loop;
        }
        case opcode::Cases2: {
            /** Instruction: cases2 pc1 pc2

                stack before,              after
                ...                        ...
                v                 ==>      v
                (#i a_1 ... a_n)           a_1
                ...
                a_n

                m_pc := pc1  if  i == 0
                := pc2  if  i == 1
            */
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            push_fields(top);
            m_pc = instr.get_cases2_pc(cidx(top));
            goto main_loop;
        }
        case opcode::NatCases: {
            /** Instruction: natcases pc1 pc2

                stack before,              after (if n = 0)    after (if n > 0)
                ...                        ...                 ...
                v                 ==>      v                   v
                n                                              n-1

                m_pc := pc1  if  n == 0
                := pc2  if  otherwise
            */
            vm_obj & top = m_stack.back();
            if (is_simple(top)) {
                unsigned val = cidx(top);
                if (val == 0) {
                    m_stack.pop_back();
                    m_pc++;
                    goto main_loop;
                } else {
                    vm_obj new_value = mk_vm_simple(val - 1);
                    swap(top, new_value);
                    m_pc = instr.get_cases2_pc(1);
                    goto main_loop;
                }
            } else {
                mpz const & val = to_mpz(top);
                if (val == 0) {
                    m_stack.pop_back();
                    m_pc++;
                    goto main_loop;
                } else {
                    vm_obj new_value = mk_vm_mpz(val - 1);
                    swap(top, new_value);
                    m_pc = instr.get_cases2_pc(1);
                    goto main_loop;
                }
            }
        }
        case opcode::CasesN: {
            /** Instruction: casesn pc_0 ... pc_[n-1]

                stack before,              after
                ...                        ...
                v                 ==>      v
                (#i a_1 ... a_n)           a_1
                ...
                a_n

                m_pc := pc_i
            */
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            push_fields(top);
            m_pc = instr.get_casesn_pc(cidx(top));
            goto main_loop;
        }
        case opcode::BuiltinCases: {
            /** Instruction: builtin_cases
                It is similar to CasesN, but uses the vm_cases_function to extract the data.
            */
            vm_obj top = m_stack.back();
            m_stack.pop_back();
            vm_cases_function fn = get_builtin_cases(instr.get_cases_idx());
            buffer<vm_obj> data;
            unsigned cidx = fn(top, data);
            std::copy(data.begin(), data.end(), std::back_inserter(m_stack));
            m_pc = instr.get_casesn_pc(cidx);
            goto main_loop;
        }
        case opcode::Proj: {
            /** Instruction: proj i

               stack before,              after
               ...                        ...
               v                     ==>  v
               (#i a_0 ... a_{n-1})       a_i

            */
            vm_obj & top = m_stack.back();
            top = cfield(top, instr.get_idx());
            m_pc++;
            goto main_loop;
        }
        case opcode::Unreachable:
            throw exception("VM unreachable instruction has been reached");
        case opcode::Ret: {
            /**
               Instruction: ret

               call stack before                  after

               ...                                ...
               (code, fn_idx, num, pc, bp)  ==>

               Restore m_code, m_fn_idx, m_pc, m_bp with top of call stack.

               stack before        after
               ...                 ...
               v                   v
               a_n                 r
               ...       ==>
               a_1
               r


               a_1, ... a_n were the arguments for the function call.
               r is the result.
            */
            lean_assert(!m_call_stack.empty());
            frame const & fr = m_call_stack.back();
            unsigned sz      = m_stack.size();
            lean_assert(sz - fr.m_num - 1 < m_stack.size());
            lean_assert(sz - 1 < m_stack.size());
            swap(m_stack[sz - fr.m_num - 1], m_stack[sz - 1]);
            m_stack.resize(sz - fr.m_num);
            m_code   = fr.m_code;
            m_fn_idx = fr.m_fn_idx;
            m_pc     = fr.m_pc;
            m_bp     = fr.m_bp;
            if (m_call_stack.size() == init_call_stack_sz) {
                m_call_stack.pop_back();
                return;
            } else {
                m_call_stack.pop_back();
                goto main_loop;
            }
        }
        case opcode::Apply: {
            /**
               Instruction: apply

               We keep consuming 'apply' instructions until the next instruction is not an 'apply'
               or we have enough arguments for executing the closure.

               stack before
               ...
               v
               a_n
               ...                       ==>
               a_1
               (closure fn b_m ... b_1)

               Case 1)
               Suppose we have n consecutive 'apply' instructions and arity of fn < n+m


               Then,

               stack after
                                       ...
               =>                      v
                                       (closure fn a_n ... a_1 b_m ... b_1)

               Case 2) arity of fn = n + m
               Then, see InvokeGlobal (if fn is global) and InvokeBuiltin (if fn is builtin)
            */
            unsigned sz       = m_stack.size();
            vm_obj closure    = m_stack.back();
            m_stack.pop_back();
            unsigned fn_idx   = cfn_idx(closure);
            vm_decl d         = get_decl(fn_idx);
            unsigned csz      = csize(closure);
            unsigned arity    = d.get_arity();
            lean_assert(csz < arity);
            unsigned nargs    = csz + 1;
            lean_assert(nargs <= arity);
            /* Keep consuming 'apply' instructions while nargs < arity */
            while (nargs < arity && m_code[m_pc+1].op() == opcode::Apply) {
                nargs++;
                m_pc++;
            }
            /* Copy closure data to the top of the stack */
            std::copy(cfields(closure), cfields(closure) + csz, std::back_inserter(m_stack));
            if (nargs < arity) {
                /* Case 1) We don't have sufficient arguments. So, we create a new closure */
                sz = m_stack.size();
                vm_obj new_value = mk_vm_closure(fn_idx, nargs, m_stack.data() + sz - nargs);
                m_stack.resize(sz - nargs + 1);
                swap(m_stack.back(), new_value);
                m_pc++;
                goto main_loop;
            } else {
                lean_assert(nargs == arity);
                /* Case 2 */
                invoke(d);
                goto main_loop;
            }
        }
        case opcode::InvokeGlobal: {
            check_interrupted();
            check_memory("vm");
            /**
               Instruction: ginvoke fn

               call stack before                  after

               ...              ==>               ...
                                                  (fn.m_code, fn.idx, fn.arity, m_pc+1, m_bp)

               Update m_code, m_fn_idx, with fn, and update m_pc := 0, m_bp

               stack before            after
               ...                     ...
               v                       v
               a_n              m_bp : a_n
               ...       ==>           ...
               a_1                     a_1

               where n is fn.arity
            */
            vm_decl decl = get_decl(instr.get_fn_idx());
            invoke_global(decl);
            goto main_loop;
        }
        case opcode::InvokeBuiltin: {
            check_interrupted();
            check_memory("vm");
            /**
               Instruction: builtin fn

               stack before          after
               ...                   ...
               v                     v
               a_n                   r
               ...       ==>
               a_1

               where n is fn.arity

               Remark: note that the arguments are in reverse order.
            */
            vm_decl decl = get_decl(instr.get_fn_idx());
            invoke_builtin(decl);
            goto main_loop;
        }
        case opcode::InvokeCFun: {
            check_interrupted();
            check_memory("vm");
            /**
               Instruction: cfun fn

               Similar to InvokeBuiltin
            */
            vm_decl decl = get_decl(instr.get_fn_idx());
            invoke_cfun(decl);
            goto main_loop;
        }}
    }
}

void vm_state::invoke_fn(name const & fn) {
    if (auto r = m_fn_name2idx.find(fn)) {
        invoke_fn(*r);
    } else {
        throw exception(sstream() << "VM does not have code for '" << fn << "'");
    }
}

void vm_state::invoke_fn(unsigned fn_idx) {
    vm_decl d      = get_decl(fn_idx);
    unsigned arity = d.get_arity();
    if (arity > m_stack.size())
        throw exception("invalid VM function call, data stack does not have enough values");
    invoke(d);
    run();
}

vm_obj vm_state::get_constant(name const & cname) {
    if (auto fn_idx = m_fn_name2idx.find(cname)) {
        vm_decl d = get_decl(*fn_idx);
        if (d.get_arity() == 0) {
            DEBUG_CODE(unsigned stack_sz = m_stack.size(););
            unsigned saved_pc = m_pc;
            invoke(d);
            run();
            vm_obj r = m_stack.back();
            m_stack.pop_back();
            m_pc = saved_pc;
            lean_assert(m_stack.size() == stack_sz);
            return r;
        } else {
            return mk_vm_closure(*fn_idx, 0, nullptr);
        }
    } else {
        throw exception(sstream() << "VM does not have code for '" << cname << "'");
    }
}

void vm_state::execute(vm_instr const * code) {
    m_call_stack.emplace_back(m_code, m_fn_idx, 0, m_pc, m_bp);
    m_code            = code;
    m_fn_idx          = -1;
    m_pc              = 0;
    m_bp              = m_stack.size();
    run();
}

void vm_state::apply(unsigned n) {
    buffer<vm_instr> code;
    for (unsigned i = 0; i < n; i++)
        code.push_back(mk_apply_instr());
    code.push_back(mk_ret_instr());
    execute(code.data());
}

void vm_state::display(std::ostream & out, vm_obj const & o) const {
    ::lean::display(out, o,
                    [&](unsigned idx) { return optional<name>(get_decl(idx).get_name()); });
}

optional<vm_decl> vm_state::get_decl(name const & n) const {
    if (auto idx = m_fn_name2idx.find(n))
        return optional<vm_decl>(get_decl(*idx));
    else
        return optional<vm_decl>();
}

void display_vm_code(std::ostream & out, environment const & env, unsigned code_sz, vm_instr const * code) {
    vm_decls const & ext = get_extension(env);
    auto idx2name = [&](unsigned idx) {
        if (idx < ext.m_decls.size()) {
            return optional<name>(ext.m_decls.find(idx)->get_name());
        } else {
            return optional<name>();
        }
    };
    auto cases2name = [&](unsigned idx) {
        if (idx < ext.m_cases_names.size()) {
            return optional<name>(*ext.m_cases_names.find(idx));
        } else {
            return optional<name>();
        }
    };

    for (unsigned i = 0; i < code_sz; i++) {
        out << i << ": ";
        code[i].display(out, idx2name, cases2name);
        out << "\n";
    }
}

char const * get_vm_builtin_internal_name(name const & fn) {
    if (auto p = g_vm_builtins->find(fn))
        return std::get<1>(*p);
    if (auto p = g_vm_cbuiltins->find(fn))
        return std::get<1>(*p);
    if (auto p = g_vm_cases_builtins->find(fn))
        return std::get<0>(*p);
    return nullptr;
}

vm_builtin_kind get_vm_builtin_kind(name const & fn) {
    if (g_vm_builtins->contains(fn))
        return vm_builtin_kind::VMFun;
    if (g_vm_cbuiltins->contains(fn))
        return vm_builtin_kind::CFun;
    if (g_vm_cases_builtins->contains(fn))
        return vm_builtin_kind::Cases;
    lean_unreachable();
}

unsigned get_vm_builtin_arity(name const & fn) {
    if (auto p = g_vm_cbuiltins->find(fn))
        return std::get<0>(*p);
    lean_unreachable();
}

void initialize_vm_core() {
    g_vm_builtins = new name_map<std::tuple<unsigned, char const *, vm_function>>();
    g_vm_cbuiltins = new name_map<std::tuple<unsigned, char const *, vm_cfunction>>();
    g_vm_cases_builtins = new name_map<std::tuple<char const *, vm_cases_function>>();
    g_may_update_vm_builtins = true;
    DEBUG_CODE({
            /* We only trace VM in debug mode because it produces a 10% performance penalty */
            register_trace_class("vm");
            register_trace_class({"vm", "run"});
        });
}

void finalize_vm_core() {
    delete g_vm_builtins;
    delete g_vm_cbuiltins;
    delete g_vm_cases_builtins;
}

void initialize_vm() {
    g_ext = new vm_decls_reg();
    // g_may_update_vm_builtins = false;
    g_vm_reserve_key = new std::string("VMR");
    g_vm_code_key    = new std::string("VMC");
    register_module_object_reader(*g_vm_reserve_key, reserve_reader);
    register_module_object_reader(*g_vm_code_key, code_reader);
}

void finalize_vm() {
    delete g_ext;
    delete g_vm_reserve_key;
    delete g_vm_code_key;
}
}

void print(lean::vm_obj const & o) {
    ::lean::display(std::cout, o);
    std::cout << "\n";
}
