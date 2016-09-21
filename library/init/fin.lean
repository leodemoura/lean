/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.nat
open Nat
structure Fin (n : Nat) := (val : Nat) (is_lt : val < n)

namespace Fin

variable {n : Nat}

lemma eq_of_veq : ∀ {i j : Fin n}, (val i) = (val j) → i = j
| ⟨iv, ilt₁⟩ ⟨.iv, ilt₂⟩ rfl := rfl

lemma veq_of_eq : ∀ {i j : Fin n}, i = j → (val i) = (val j)
| ⟨iv, ilt⟩ .⟨iv, ilt⟩ rfl := rfl

end Fin

open Fin

attribute [instance]
protected definition decidableEqFin (n : Nat) : DecidableEq (Fin n)
| ⟨ival, ilt⟩ ⟨jval, jlt⟩ :=
  match decidableEqNat ival jval with
  | is_true  h₁ := is_true (eq_of_veq h₁)
  | is_false h₁ := is_false (λ h₂, absurd (veq_of_eq h₂) h₁)
  end
