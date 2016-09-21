/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.fin

open Nat

definition charSz : Nat := succ 255
definition Char : Type := Fin charSz

namespace Char
/- We cannot use tactic dec_trivial here because the tactic framework has not been defined yet. -/
private lemma zero_lt_charSz : 0 < charSz :=
zero_lt_succ _

attribute [pattern]
definition ofNat (n : Nat) : Char :=
if h : n < charSz then ⟨n, h⟩ else ⟨0, zero_lt_charSz⟩

definition toNat (c : Char) : Nat :=
Fin.val c
end Char

attribute [instance]
definition decidableEqChar : DecidableEq Char :=
have DecidableEq (Fin charSz), from decidableEqFin _,
this

attribute [instance]
definition inhabitedChar : Inhabited Char :=
⟨'A'⟩
