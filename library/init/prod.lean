/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.num init.relation
universe variables u v

notation A × B := Prod A B
-- notation for n-ary tuples
notation `(` h `, ` t:(foldr `, ` (e r, Prod.mk e r)) `)` := Prod.mk h t

namespace Prod
  notation `pr₁` := pr1
  notation `pr₂` := pr2
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2

end Prod

attribute [instance]
protected definition inhabitedProd {A : Type u} {B : Type v} [Inhabited A] [Inhabited B] : Inhabited (Prod A B) :=
⟨(default A, default B)⟩

attribute [instance]
protected definition decidableEqProd {A : Type u} {B : Type v} [h₁ : DecidableEq A] [h₂ : DecidableEq B] : DecidableEq (Prod A B)
| (a, b) (a', b') :=
  match (h₁ a a') with
  | (is_true e₁) :=
    match (h₂ b b') with
    | (is_true e₂)  := is_true (eq.rec_on e₁ (eq.rec_on e₂ rfl))
    | (is_false n₂) := is_false (assume h, Prod.no_confusion h (λ e₁' e₂', absurd e₂' n₂))
    end
  | (is_false n₁) := is_false (assume h, Prod.no_confusion h (λ e₁' e₂', absurd e₁' n₁))
  end
