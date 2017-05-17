/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import .basic init.data.nat init.data.fn_array.lemmas
universes u w

namespace array
variables {α : Type u} {β : Type w} {n : nat}

lemma read_eq_read' [inhabited α] (a : array α n) (i : nat) (h : i < n) : read a ⟨i, h⟩ = read' a i :=
by unfold read read'; apply fn_array.read_eq_read'

lemma write_eq_write' (a : array α n) (i : nat) (h : i < n) (v : α) : write a ⟨i, h⟩ v = write' a i v :=
by unfold write write'; apply congr_arg; apply fn_array.write_eq_write'

theorem rev_list_reverse (a : array α n) : a.rev_list.reverse = a.to_list :=
by unfold rev_list; apply fn_array.rev_list_reverse

theorem to_list_reverse (a : array α n) : a.to_list.reverse = a.rev_list :=
by unfold to_list; apply fn_array.to_list_reverse

theorem rev_list_length (a : array α n) : a.rev_list.length = n :=
by unfold rev_list; apply fn_array.rev_list_length

theorem to_list_length (a : array α n) : a.to_list.length = n :=
by unfold to_list; apply fn_array.to_list_length

theorem to_list_nth (a : array α n) (i : ℕ) (h h') : list.nth_le a.to_list i h' = a.read ⟨i, h⟩ :=
by unfold to_list; apply fn_array.to_list_nth

theorem mem_iff_rev_list_mem (a : array α n) (v : α) : v ∈ a ↔ v ∈ a.rev_list :=
by unfold mem; apply fn_array.mem_iff_rev_list_mem

theorem mem_iff_list_mem (a : array α n) (v : α) : v ∈ a ↔ v ∈ a.to_list :=
by rw -rev_list_reverse; simp[mem_iff_rev_list_mem]

@[simp] def to_list_to_array (a : array α n) : a.to_list.to_array == a :=
begin
  cases a with f,
  unfold to_list list.to_array,
  note := fn_array.to_list_length f,
  note := fn_array.to_list_to_fn_array f,
  cc
end

@[simp] def to_array_to_list (l : list α) : l.to_array.to_list = l :=
by unfold to_list list.to_array; apply fn_array.to_fn_array_to_list

end array
