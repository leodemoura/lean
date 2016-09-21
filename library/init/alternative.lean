/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic init.applicative
universe variables u v

structure [class] Alternative (F : Type u → Type v) extends Applicative F : Type (max u+1 v) :=
(failure : Π {A : Type u}, F A)
(orelse  : Π {A : Type u}, F A → F A → F A)

attribute [inline]
definition failure {F : Type u → Type v} [Alternative F] {A : Type u} : F A :=
Alternative.failure F

attribute [inline]
definition orelse {F : Type u → Type v} [Alternative F] {A : Type u} : F A → F A → F A :=
Alternative.orelse

infixr ` <|> `:2 := orelse

attribute [inline]
definition guard {F : Type → Type v} [Alternative F] (P : Prop) [Decidable P] : F Unit :=
if P then pure () else failure
