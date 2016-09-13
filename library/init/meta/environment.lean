/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.declaration init.meta.exceptional

meta_constant environment : Type₁

namespace environment
/- Create a standard environment using the given trust level -/
meta_constant mk_std          : nat → environment
/- Create a HoTT environment -/
meta_constant mk_hott         : nat → environment
/- Return the trust level of the given environment -/
meta_constant trust_lvl       : environment → nat
/- Return tt iff it is a standard environment -/
meta_constant is_std          : environment → bool
/- Add a new declaration to the environment -/
meta_constant add             : environment → declaration → exceptional environment
/- Retrieve a declaration from the environment -/
meta_constant get             : environment → name → exceptional declaration
/- Add a new inductive datatype to the environment
   name, universe parameters, number of parameters, type, constructors (name and type) -/
meta_constant add_inductive   : environment → name → list name → nat → expr → list (name × expr) → exceptional environment
/- Return tt iff the given name is an inductive datatype -/
meta_constant is_inductive    : environment → name → bool
/- Return tt iff the given name is a constructor -/
meta_constant is_constructor  : environment → name → bool
/- Return tt iff the given name is a recursor -/
meta_constant is_recursor     : environment → name → bool
/- Return tt iff the given name is a recursive inductive datatype -/
meta_constant is_recursive    : environment → name → bool
/- Return the name of the inductive datatype of the given constructor. -/
meta_constant inductive_type_of : environment → name → option name
/- Return the constructors of the inductive datatype with the given name -/
meta_constant constructors_of : environment → name → list name
/- Return the recursor of the given inductive datatype -/
meta_constant recursor_of     : environment → name → option name
/- Return the number of parameters of the inductive datatype -/
meta_constant inductive_num_params : environment → name → nat
/- Return the number of indices of the inductive datatype -/
meta_constant inductive_num_indices : environment → name → nat
/- Fold over declarations in the environment -/
meta_constant fold {A :Type} : environment → A → (declaration → A → A) → A
/- (relation_info env n) returns some value if n is marked as a relation in the given environment.
   the tuple contains: total number of arguments of the relation, lhs position and rhs position. -/
meta_constant relation_info : environment → name → option (nat × nat × nat)
/- (refl_for env R) returns the name of the reflexivity theorem for the relation R -/
meta_constant refl_for : environment → name → option name
/- (symm_for env R) returns the name of the symmetry theorem for the relation R -/
meta_constant symm_for : environment → name → option name
/- (trans_for env R) returns the name of the transitivity theorem for the relation R -/
meta_constant trans_for : environment → name → option name
open expr

meta_definition is_constructor_app (env : environment) (e : expr) : bool :=
is_constant (get_app_fn e) && is_constructor env (const_name (get_app_fn e))

meta_definition is_refl_app (env : environment) (e : expr) : option (name × expr × expr) :=
match (refl_for env (const_name (get_app_fn e))) with
| (some n) :=
    if get_app_num_args e ≥ 2
    then some (n, app_arg (app_fn e), app_arg e)
    else none
| none   := none
end
end environment

attribute [instance]
meta_definition environment.has_to_string : has_to_string environment :=
has_to_string.mk (λ e, "[environment]")

attribute [instance]
meta_definition environment.is_inhabited : inhabited environment :=
inhabited.mk (environment.mk_std 0)
