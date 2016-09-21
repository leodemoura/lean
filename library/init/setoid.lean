/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura
-/
prelude
import init.relation
universe variables u
structure [class] Setoid (A : Type u) :=
(r : A → A → Prop) (iseqv : equivalence r)

infix ` ≈ ` := Setoid.r

variable {A : Type u}
variable [Setoid A]

attribute [refl]
theorem setoid_refl (a : A) : a ≈ a :=
match Setoid.iseqv A with
| ⟨h_refl, h_symm, h_trans⟩ := h_refl a
end

attribute [symm]
theorem setoid_symm {a b : A} (Hab : a ≈ b) : b ≈ a :=
match Setoid.iseqv A with
| ⟨h_refl, h_symm, h_trans⟩ := h_symm Hab
end

attribute [trans]
theorem setoid_trans {a b c : A} (Hab : a ≈ b) (Hbc : b ≈ c) : a ≈ c :=
match Setoid.iseqv A with
| ⟨h_refl, h_symm, h_trans⟩ := h_trans Hab Hbc
end
