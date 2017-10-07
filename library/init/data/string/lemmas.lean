/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta
import init.data.array.lemmas

namespace string
lemma empty_ne_str (c : char) (s : string) : empty ≠ str s c :=
begin cases s, unfold str empty, intro h, injection h, contradiction end

lemma str_ne_empty (c : char) (s : string) : str s c ≠ empty :=
begin cases s, unfold str empty, intro h, injection h, contradiction end

lemma str_ne_str_left {c₁ c₂ : char} (s₁ s₂ : string) : c₁ ≠ c₂ → str s₁ c₁ ≠ str s₂ c₂ :=
begin
  cases s₁ with n₁ a₁,
  cases s₂ with n₂ a₂,
  unfold str,
  intros h₁ h₂,
  injection h₂ with h₂₁ h₂₂,
  injection h₂₁,
  subst n₂,
  have: a₁.push_back c₁ = a₂.push_back c₂, from eq_of_heq h₂₂,
  have: c₁ = c₂, from array.push_back_inj_right this,
  contradiction
end

lemma str_ne_str_right (c₁ c₂ : char) {s₁ s₂ : string} : s₁ ≠ s₂ → str s₁ c₁ ≠ str s₂ c₂ :=
begin
  cases s₁ with n₁ a₁,
  cases s₂ with n₂ a₂,
  unfold str,
  intros h₁ h₂,
  injection h₂ with h₂₁ h₂₂,
  injection h₂₁,
  subst n₂,
  have: a₁.push_back c₁ = a₂.push_back c₂, from eq_of_heq h₂₂,
  have: a₁ = a₂, from array.push_back_inj_left this,
  subst a₁,
  contradiction
end
end string
