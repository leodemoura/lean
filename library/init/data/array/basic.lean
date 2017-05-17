/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import init.data.fn_array.basic
universes u w

structure array (α : Type u) (n : nat) :=
(data : fn_array α n)

def mk_array {α} (n) (v : α) : array α n :=
{data := mk_fn_array n v}

namespace array
variables {α : Type u} {β : Type w} {n : nat}

def nil {α} : array α 0 :=
{data := fn_array.nil}

def read (a : array α n) (i : fin n) : α :=
a.data.read i

def read' [inhabited α] (a : array α n) (i : nat) : α :=
a.data.read' i

def write (a : array α n) (i : fin n) (v : α) : array α n :=
{data := a.data.write i v}

def write' (a : array α n) (i : nat) (v : α) : array α n :=
{data := a.data.write' i v}

def push_back (a : array α n) (v : α) : array α (n+1) :=
{data := a.data.push_back v}

def pop_back (a : array α (n+1)) : array α n :=
{data := a.data.pop_back}

@[elab_as_eliminator]
theorem write_ind (a : array α n) (i : fin n) (v : α) (C : fin n → α → Sort w)
  (Hi : C i v) (Hj : ∀j, i ≠ j → C j (a.read j)) (j) : C j ((a.write i v).read j) :=
show C j (if i = j then v else read a j), from
if h : i = j then by rwa [if_pos h, -h]
else by rw [if_neg h]; exact Hj j h

def foreach (a : array α n) (f : fin n → α → α) : array α n :=
{data := a.data.foreach f}

def map (f : α → α) (a : array α n) : array α n :=
foreach a (λ _, f)

def map₂ (f : α → α → α) (a b : array α n) : array α n :=
foreach b (λ i, f (a.read i))

def iterate_aux (a : array α n) (f : fin n → α → β → β) : Π (i : nat), i ≤ n → β → β :=
a.data.iterate_aux f

def iterate (a : array α n) (b : β) (fn : fin n → α → β → β) : β :=
a.data.iterate b fn

def foldl (a : array α n) (b : β) (f : α → β → β) : β :=
a.data.foldl b f

def rev_list (a : array α n) : list α :=
a.data.rev_list

def foldl_eq (a : array α n) (b : β) (f : α → β → β) : a.foldl b f = a.rev_list.foldr f b :=
by cases a; apply fn_array.foldl_eq

def rev_iterate (a : array α n) (b : β) (fn : fin n → α → β → β) : β :=
a.data.rev_iterate b fn

def to_list (a : array α n) : list α :=
a.data.to_list

protected def mem (v : α) (a : array α n) : Prop :=
a.data.mem v

instance : has_mem α (array α n) := ⟨array.mem⟩

theorem read_mem (a : array α n) (i) : read a i ∈ a :=
exists.intro i rfl

instance [has_to_string α] : has_to_string (array α n) :=
⟨to_string ∘ to_list⟩

meta instance [has_to_format α] : has_to_format (array α n) :=
⟨to_fmt ∘ to_list⟩

meta instance [has_to_tactic_format α] : has_to_tactic_format (array α n) :=
⟨tactic.pp ∘ to_list⟩

end array

def list.to_array {α} (l : list α) : array α l.length :=
{data := list.to_fn_array l}
