/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
prelude
import init.data.fin.basic
import init.data.nat.basic
import init.data.list.basic
universes u w

structure array (α : Type u) (n : nat) :=
(data : fin n → α)

def mk_array {α} (n) (v : α) : array α n :=
{data := λ _, v}

namespace array
variables {α : Type u} {β : Type w} {n : nat}

def nil {α} : array α 0 :=
{data := λ ⟨x, h⟩, absurd h (nat.not_lt_zero x)}

def read (a : array α n) (i : fin n) : α :=
a.data i

def read' [inhabited α] (a : array α n) (i : nat) : α :=
if h : i < n then a.read ⟨i,h⟩ else default α

def write (a : array α n) (i : fin n) (v : α) : array α n :=
{data := λ j, if i = j then v else a.read j}

def write' (a : array α n) (i : nat) (v : α) : array α n :=
if h : i < n then a.write ⟨i, h⟩ v else a

lemma push_back_idx {j n} (h₁ : j < n + 1) (h₂ : j ≠ n) : j < n :=
nat.lt_of_le_of_ne (nat.le_of_lt_succ h₁) h₂

def push_back (a : array α n) (v : α) : array α (n+1) :=
{data := λ ⟨j, h₁⟩, if h₂ : j = n then v else a.read ⟨j, push_back_idx h₁ h₂⟩}

lemma pop_back_idx {j n} (h : j < n) : j < n + 1 :=
nat.lt.step h

def pop_back (a : array α (n+1)) : array α n :=
{data := λ ⟨j, h⟩, a.read ⟨j, pop_back_idx h⟩}

def iterate_aux (a : array α n) (f : fin n → α → β → β) : Π (i : nat), i ≤ n → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin n := ⟨j, h⟩ in
  f i (a.read i) (iterate_aux j (nat.le_of_lt h) b)

def iterate (a : array α n) (b : β) (fn : fin n → α → β → β) : β :=
iterate_aux a fn n (nat.le_refl _) b

def foreach (a : array α n) (f : fin n → α → α) : array α n :=
iterate a a (λ i v a', a'.write i (f i v))

def map (f : α → α) (a : array α n) : array α n :=
foreach a (λ _, f)

def map₂ (f : α → α → α) (a b : array α n) : array α n :=
foreach b (λ i, f (a.read i))

def foldl (a : array α n) (b : β) (f : α → β → β) : β :=
iterate a b (λ _, f)

def rev_list (a : array α n) : list α :=
a.foldl [] (λ v l, v :: l)

def foldl_eq_aux (a : array α n) (b : β) (f : α → β → β) :
  Π (i : nat) (h : i ≤ n), iterate_aux a (λ _, f) i h b = (iterate_aux a (λ _ v l, v :: l) i h []).foldr f b
| 0     h := rfl
| (j+1) h := congr_arg (f (read a ⟨j, h⟩)) (foldl_eq_aux j _)

def foldl_eq (a : array α n) (b : β) (f : α → β → β) : a.foldl b f = a.rev_list.foldr f b :=
foldl_eq_aux a b f _ _

def rev_iterate_aux (a : array α n) (f : fin n → α → β → β) : Π (i : nat), i ≤ n → β → β
| 0     h b := b
| (j+1) h b :=
  let i : fin n := ⟨j, h⟩ in
  rev_iterate_aux j (nat.le_of_lt h) (f i (a.read i) b)

def rev_iterate (a : array α n) (b : β) (fn : fin n → α → β → β) : β :=
rev_iterate_aux a fn n (nat.le_refl _) b

def to_list (a : array α n) : list α :=
a.rev_iterate [] (λ _ v l, v :: l)

protected def mem (v : α) (a : array α n) : Prop := ∃i, read a i = v

instance : has_mem α (array α n) := ⟨array.mem⟩

theorem read_mem (a : array α n) (i) : read a i ∈ a := exists.intro i rfl
end array
