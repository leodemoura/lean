/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.fin

open Nat

definition unsignedSz : Nat := succ 4294967295

attribute [reducible]
definition Unsigned := Fin unsignedSz

namespace Unsigned
/- We cannot use tactic dec_trivial here because the tactic framework has not been defined yet. -/
private lemma zero_lt_unsignedSz : 0 < unsignedSz :=
zero_lt_succ _

definition ofNat (n : Nat) : Unsigned :=
if h : n < unsignedSz then ⟨n, h⟩ else ⟨0, zero_lt_unsignedSz⟩

definition toNat (c : Unsigned) : Nat :=
Fin.val c
end Unsigned

attribute [instance]
definition decidableEqUnsigned : DecidableEq Unsigned :=
have DecidableEq (Fin unsignedSz), from decidableEqFin _,
this
