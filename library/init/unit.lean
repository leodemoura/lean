/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic

theorem unit_eq (a b : Unit) : a = b :=
Unit.rec_on a (Unit.rec_on b rfl)

theorem unit_eq_unit (a : Unit) : a = () :=
unit_eq a ()

attribute [instance]
definition subsingletonUnit : subsingleton Unit :=
subsingleton.intro unit_eq

attribute [instance]
definition inhabitedUnit : Inhabited Unit :=
⟨()⟩
