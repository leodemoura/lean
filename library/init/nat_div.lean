/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.wf init.nat

namespace Nat

private definition div_rec_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
λ h, and.rec (λ ypos ylex, sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos) h

private definition divF (x : Nat) (f : Π x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma H) y + 1 else zero

protected definition div := well_founded.fix lt_wf divF

attribute [instance]
definition divNat : Div Nat :=
⟨Nat.div⟩

theorem div_def (x y : Nat) : div x y = if H : 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
congr_fun (well_founded.fix_eq lt_wf divF x) y

private definition modF (x : Nat) (f : Π x₁, x₁ < x → Nat → Nat) (y : Nat) : Nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma H) y else x

protected definition mod := well_founded.fix lt_wf modF

attribute [instance]
definition modNat : Mod Nat :=
⟨Nat.mod⟩

theorem mod_def (x y : Nat) : mod x y = if H : 0 < y ∧ y ≤ x then mod (x - y) y else x :=
congr_fun (well_founded.fix_eq lt_wf modF x) y

end Nat
