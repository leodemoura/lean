/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson and Jared Roesch
-/
prelude
import init.applicative init.string init.trace
universe variables u v

structure [class] Monad (M : Type u → Type v) extends Functor M : Type (max u+1 v) :=
(ret  : Π {A : Type u}, A → M A)
(bind : Π {A B : Type u}, M A → (A → M B) → M B)

attribute [inline]
definition return {M : Type u → Type v} [Monad M] {A : Type u} : A → M A :=
Monad.ret M

definition fapp {M : Type u → Type v} [Monad M] {A B : Type u} (f : M (A → B)) (a : M A) : M B :=
do g ← f,
   b ← a,
   return (g b)

attribute [inline, instance]
definition Monad.applicative (M : Type u → Type v) [Monad M] : Applicative M :=
Applicative.mk (@fmap _ _) (@return _ _) (@fapp _ _)

attribute [inline]
definition Monad.andThen {A B : Type u} {M : Type u → Type v} [Monad M] (a : M A) (b : M B) : M B :=
do a, b

infixl ` >>= `:2 := Monad.bind
infixl ` >> `:2  := Monad.andThen
