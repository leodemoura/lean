/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.char init.list
attribute [reducible]
definition String := List Char

namespace String

attribute [pattern]
definition empty : String := List.nil

attribute [pattern]
definition str : Char → String → String := List.cons

definition concat (a b : String) : String :=
List.append b a
end String

attribute [instance]
definition appendString: Append String :=
⟨String.concat⟩

open List

private definition utf8LengthAux : Nat → Nat → String → Nat
| 0 r (c::s) :=
  let n := Char.toNat c in
  if                 n < 0x80 then utf8LengthAux 0 (r+1) s
  else if 0xC0 ≤ n ∧ n < 0xE0 then utf8LengthAux 1 (r+1) s
  else if 0xE0 ≤ n ∧ n < 0xF0 then utf8LengthAux 2 (r+1) s
  else if 0xF0 ≤ n ∧ n < 0xF8 then utf8LengthAux 3 (r+1) s
  else if 0xF8 ≤ n ∧ n < 0xFC then utf8LengthAux 4 (r+1) s
  else if 0xFC ≤ n ∧ n < 0xFE then utf8LengthAux 5 (r+1) s
  else                             utf8LengthAux 0 (r+1) s
| (n+1) r (c::s) := utf8LengthAux n r s
| n     r []     := r

definition utf8Length : String → Nat
| s := utf8LengthAux 0 0 (reverse s)
