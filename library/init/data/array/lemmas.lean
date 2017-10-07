/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.array.basic
import init.data.nat

namespace array
universes u w
variables {α : Type u} {β : Type w} {n m : nat}

lemma read_eq_read' [inhabited α] (a : array α n) (i : nat) (h : i < n) : read a ⟨i, h⟩ = read' a i :=
by unfold read'; rw [dif_pos h]

lemma write_eq_write' (a : array α n) (i : nat) (h : i < n) (v : α) : write a ⟨i, h⟩ v = write' a i v :=
by unfold write'; rw [dif_pos h]

lemma lt_aux_1 {a b c : nat} (h : a + c < b) : a < b :=
lt_of_le_of_lt (nat.le_add_right a c) h

lemma lt_aux_2 {n} (h : n > 0) : n - 1 < n :=
have h₁ : 1 > 0, from dec_trivial,
nat.sub_lt h h₁

lemma lt_aux_3 {n i} (h : i + 1 < n) : n - 2 - i < n  :=
have n > 0,     from lt.trans (nat.zero_lt_succ i) h,
have n - 2 < n, from nat.sub_lt this (dec_trivial),
lt_of_le_of_lt (nat.sub_le _ _) this

@[elab_as_eliminator]
theorem write_ind (a : array α n) (i : fin n) (v : α) (C : fin n → α → Sort w)
  (Hi : C i v) (Hj : ∀j, i ≠ j → C j (a.read j)) (j) : C j ((a.write i v).read j) :=
show C j (if i = j then v else read a j), from
if h : i = j then by rwa [if_pos h, ← h]
else by rw [if_neg h]; exact Hj j h

lemma read_push_back (a : array α n) (c : α) : (a.push_back c).read ⟨n, nat.lt_succ_self n⟩ = c :=
by simp [push_back, read]

lemma read_push_back_of_lt (a : array α n) (c : α) {i : nat} (h₁ : i < n + 1) (h₂ : i < n) : (a.push_back c).read ⟨i, h₁⟩ = a.read ⟨i, h₂⟩  :=
begin
  have: i ≠ n, from ne_of_lt h₂,
  simp [push_back, read, this]
end

lemma push_back_inj_left {a₁ a₂ : array α n} {c₁ c₂ : α} (h : a₁.push_back c₁ = a₂.push_back c₂) : a₁ = a₂ :=
begin
  cases a₁ with d₁,
  cases a₂ with d₂,
  congr, apply funext, intro i,
  cases i with j hlt₁,
  have hlt₂ : j < n + 1, from nat.lt.step hlt₁,
  have: (push_back {data := d₁} c₁).read ⟨j, hlt₂⟩ = (push_back {data := d₂} c₂).read ⟨j, hlt₂⟩, by simp [h],
  simp [read_push_back_of_lt _ _ hlt₂ hlt₁] at this,
  simp [read] at this,
  assumption
end

lemma push_back_inj_right {a₁ a₂ : array α n} {c₁ c₂ : α} (h : a₁.push_back c₁ = a₂.push_back c₂) : c₁ = c₂ :=
have (a₁.push_back c₁).read ⟨n, nat.lt_succ_self n⟩ = (a₂.push_back c₂).read ⟨n, nat.lt_succ_self n⟩, by simp [h],
begin
  simp [read_push_back] at this,
  assumption
end

lemma array0_eq (a₁ a₂ : array α 0) : a₁ = a₂ :=
begin
  cases a₁, cases a₂, congr,
  apply funext, intro i,
  apply i.elim0
end

end array
