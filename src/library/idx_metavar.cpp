/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "kernel/for_each_fn.h"
#include "library/idx_metavar.h"
#include "library/replace_visitor.h"

#ifndef LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY
#define LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY 1024*8
#endif

namespace lean {
static name * g_tmp_prefix = nullptr;

void initialize_idx_metavar() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_idx_metavar() {
    delete g_tmp_prefix;
}

level mk_idx_metauniv(unsigned i) {
    return mk_meta_univ(name(*g_tmp_prefix, i));
}

expr mk_idx_metavar(unsigned i, expr const & type) {
    return mk_metavar(name(*g_tmp_prefix, i), type);
}

bool is_idx_metauniv(level const & l) {
    if (!is_meta(l))
        return false;
    name const & n = meta_id(l);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(level const & l) {
    lean_assert(is_idx_metauniv(l));
    return meta_id(l).get_numeral();
}

bool is_idx_metavar(expr const & e) {
    if (!is_metavar(e))
        return false;
    name const & n = mlocal_name(e);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(expr const & e) {
    lean_assert(is_idx_metavar(e));
    return mlocal_name(e).get_numeral();
}

bool has_idx_metauniv(level const & l) {
    if (!has_meta(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (found) return false;
            if (!has_meta(l)) return false;
            if (is_idx_metauniv(l))
                found = true;
            return true;
        });
    return found;
}

bool has_idx_metavar(expr const & e) {
    if (!has_univ_metavar(e) && !has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found) return false;
            if (!has_univ_metavar(e) && !has_expr_metavar(e)) return false;
            if (is_idx_metavar(e))
                found = true;
            else if (is_constant(e) && std::any_of(const_levels(e).begin(), const_levels(e).end(), has_idx_metauniv))
                found = true;
            else if (is_sort(e) && has_idx_metauniv(sort_level(e)))
                found = true;
            return true;
        });
    return found;
}

level lift_idx_metaunivs(level const & l, unsigned udelta) {
    if (!has_meta(l) || udelta == 0)
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l)) return some_level(l);
            if (is_idx_metauniv(l))
                return some_level(mk_idx_metauniv(to_meta_idx(l) + udelta));
            else
                return none_level();
        });
}

levels lift_idx_metaunivs(levels const & ls, unsigned udelta) {
    return map_reuse(ls,
                     [&](level const & l) { return lift_idx_metaunivs(l, udelta); },
                     [](level const & l1, level const & l2) { return is_eqp(l1, l2); });
}

class lift_idx_metavars_fn : public replace_visitor {
    unsigned m_udelta;
    unsigned m_mdelta;

    virtual expr visit_meta(expr const & m) override {
        if (is_idx_metavar(m)) {
            expr new_type = visit(mlocal_type(m));
            return mk_idx_metavar(to_meta_idx(m) + m_mdelta, new_type);
        } else {
            return replace_visitor::visit_meta(m);
        }
    }

    virtual expr visit_sort(expr const & e) override {
        return update_sort(e, lift_idx_metaunivs(sort_level(e), m_udelta));
    }

    virtual expr visit_constant(expr const & e) override {
        return update_constant(e, lift_idx_metaunivs(const_levels(e), m_udelta));
    }

    virtual expr visit(expr const & e) override {
        if ((!has_univ_metavar(e) || m_udelta == 0) && (!has_expr_metavar(e) || m_mdelta == 0))
            return e;
        return replace_visitor::visit(e);
    }
public:
    lift_idx_metavars_fn(unsigned udelta, unsigned mdelta):
        m_udelta(udelta), m_mdelta(mdelta) {
    }
};

expr lift_idx_metavars(expr const & e, unsigned udelta, unsigned mdelta) {
    // TODO(Leo): add cache if this is a performance bottleneck
    if ((!has_univ_metavar(e) || udelta == 0) && (!has_expr_metavar(e) || mdelta == 0))
        return e;
    return lift_idx_metavars_fn(udelta, mdelta)(e);
}
}
