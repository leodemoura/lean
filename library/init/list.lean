/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.nat
open Decidable List

universe variables u v

attribute [instance]
protected definition inhabitedList (A : Type u) : Inhabited (List A) :=
⟨List.nil⟩

notation h :: t  := cons h t
notation `[` l:(foldr `, ` (h t, cons h t) nil `]`) := l

namespace List
variable {A : Type u}

definition append : List A → List A → List A
| []       l := l
| (h :: s) t := h :: (append s t)

definition length : List A → Nat
| []       := 0
| (a :: l) := length l + 1

open Option Nat

definition nth : List A → Nat → Option A
| []       n     := none
| (a :: l) 0     := some a
| (a :: l) (n+1) := nth l n

definition head [Inhabited A] : List A → A
| []       := default A
| (a :: l) := a

definition tail : List A → List A
| []       := []
| (a :: l) := l

definition concat : Π (x : A), List A → List A
| a []       := [a]
| a (b :: l) := b :: concat a l

definition reverse : List A → List A
| []       := []
| (a :: l) := concat a (reverse l)

definition map {B : Type v} (f : A → B) : List A → List B
| []       := []
| (a :: l) := f a :: map l

definition join : List (List A) → List A
| []        := []
| (l :: ls) := append l (join ls)

definition filter (p : A → Prop) [h : DecidablePred p] : List A → List A
| []     := []
| (a::l) := if p a then a :: filter l else filter l

definition dropn : ℕ → List A → List A
| 0 a := a
| (succ n) [] := []
| (succ n) (x::r) := dropn n r
end List

attribute [instance]
definition appendList {A : Type u} : Append (List A) :=
⟨List.append⟩
