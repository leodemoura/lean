/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
prelude
import init.logic

notation A ⊕ B := Sum A B

universe variables u v

variables {A : Type u} {B : Type v}

attribute [instance]
protected definition is_inhabited_left [h : Inhabited A] : Inhabited (A ⊕ B) :=
⟨Sum.inl (default A)⟩

attribute [instance]
protected definition is_inhabited_right [h : Inhabited B] : Inhabited (A ⊕ B) :=
⟨Sum.inr (default B)⟩
