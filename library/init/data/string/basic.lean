/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.data.char.basic
import init.data.array.basic

private structure string_imp :=
(sz : nat) (data : array char sz)

def string := string_imp

namespace string
def empty : string :=
{sz := 0, data := array.nil}

instance : inhabited string :=
⟨empty⟩

def length : string → nat
| ⟨n, d⟩ := n

instance : has_sizeof string :=
⟨string.length⟩

def str : string → char → string
| ⟨n, d⟩ c := ⟨n+1, d.push_back c⟩

def is_empty : string → bool
| ⟨0, n⟩ := tt
| _      := ff

def to_list : string → list char
| ⟨n, d⟩ := d.to_list

def pop_back : string → string
| ⟨0,   d⟩ := ⟨0, d⟩
| ⟨n+1, d⟩ := ⟨n, d.pop_back⟩

def popn_back : string → nat → string
| s 0     := s
| s (n+1) := popn_back s.pop_back n

def fold {α} (a : α) (f : α → char → α) (s : string) : α :=
s.data.foldl a (λ c a, f a c)

def append (s₁ s₂ : string) : string :=
fold s₁ (λ r c, r.str c) s₂

instance : has_append string :=
⟨string.append⟩

def front (s : string) : char :=
s.data.read' 0

def back : string → char
| ⟨n, d⟩ := d.read' (n-1)

-- def backn : string → nat → string :=
-- sorry

def join (l : list string) : string :=
l.foldl (λ r s, r ++ s) ""

def singleton (c : char) : string :=
str empty c

end string

open list string

private def utf8_length_aux : nat → nat → list char → nat
| 0 r (c::s) :=
  let n := char.to_nat c in
  if                 n < 0x80 then utf8_length_aux 0 (r+1) s
  else if 0xC0 ≤ n ∧ n < 0xE0 then utf8_length_aux 1 (r+1) s
  else if 0xE0 ≤ n ∧ n < 0xF0 then utf8_length_aux 2 (r+1) s
  else if 0xF0 ≤ n ∧ n < 0xF8 then utf8_length_aux 3 (r+1) s
  else if 0xF8 ≤ n ∧ n < 0xFC then utf8_length_aux 4 (r+1) s
  else if 0xFC ≤ n ∧ n < 0xFE then utf8_length_aux 5 (r+1) s
  else                             utf8_length_aux 0 (r+1) s
| (n+1) r (c::s) := utf8_length_aux n r s
| n     r []     := r

def string.utf8_length : string → nat
| s := utf8_length_aux 0 0 s.to_list

export string (utf8_length)

private def to_nat_core : list char → nat → nat
| []      r := r
| (c::cs) r :=
  to_nat_core cs (char.to_nat c - char.to_nat '0' + r*10)

def string.to_nat (s : string) : nat :=
to_nat_core s.to_list 0

protected def char.to_string (c : char) : string :=
string.str "" c

def list.as_string (s : list char) : string :=
s.foldl (λ r c, r.str c) string.empty

def string.intercalate (s : string) (ss : list string) : string :=
(list.intercalate s.to_list (ss.map to_list)).as_string

/- We have to define this instance here because we need to access the internal representation,
   and string_imp is private. This is why we also have to show array has decidable equality
   without using the tactic framework. -/
instance : decidable_eq string :=
λ ⟨n₁, a₁⟩ ⟨n₂, a₂⟩,
  if h₁ : n₁ = n₂ then
    match n₁, n₂, h₁, a₁, a₂ with
    | n, _, rfl, a₁, a₂ :=
      if h₂ : a₁ = a₂ then is_true (eq.subst h₂ rfl)
      else is_false (λ h, string_imp.no_confusion h (λ e₁ e₂, absurd (eq_of_heq e₂) h₂))
    end
  else is_false (λ h, string_imp.no_confusion h (λ e₁ e₂, absurd e₁ h₁))
