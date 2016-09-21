/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.functor
universe variables u v

structure [class] Applicative (F : Type u → Type v) extends Functor F : Type (max u+1 v):=
(pure : Π {A : Type u}, A → F A)
(seq  : Π {A B : Type u}, F (A → B) → F A → F B)

attribute [inline]
definition pure {F : Type u → Type v} [Applicative F] {A : Type u} : A → F A :=
Applicative.pure F

attribute [inline]
definition seqApp {A B : Type u} {F : Type u → Type v} [Applicative F] : F (A → B) → F A → F B :=
Applicative.seq

infixr ` <*> `:2 := seqApp
