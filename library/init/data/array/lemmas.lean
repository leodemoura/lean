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
variables {α : Type u} {β : Type w} {n : nat}

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

end array
