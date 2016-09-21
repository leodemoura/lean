/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-
The elaborator tries to insert coercions automatically.
Only instances of has_coe type class are considered in the process.

Lean also provides a "lifting" operator: ↑a.
It uses all instances of has_lift type class.
Every has_coe instance is also a has_lift instance.

We recommend users only use has_coe for coercions that do not produce a lot
of ambiguity.

All coercions and lifts can be identified with the constant coe.

We use the has_coe_to_fun type class for encoding coercions from
a type to a function space.

We use the has_coe_to_sort type class for encoding coercions from
a type to a sort.
-/
prelude
import init.list init.subtype init.prod
universe variables u v

structure [class] Lift (A : Type u) (B : Type v) :=
(lift : A → B)

/- Auxiliary class that contains the transitive closure of has_lift. -/
structure [class] LiftTrans (A : Type u) (B : Type v) :=
(lift : A → B)

structure [class] Coe (A : Type u) (B : Type v) :=
(coe : A → B)

/- Auxiliary class that contains the transitive closure of has_coe. -/
structure [class] CoeTrans (A : Type u) (B : Type v) :=
(coe : A → B)

structure [class] CoeToFun (A : Type u) : Type (max u (v+1)) :=
(F : Type v) (coe : A → F)

structure [class] CoeToSort (A : Type u) : Type (max u (v+1)) :=
(S : Type v) (coe : A → S)

definition lift {A : Type u} {B : Type v} [Lift A B] : A → B :=
@Lift.lift A B _

definition coeFnBase {A : Type u} [CoeToFun.{u v} A] : A → CoeToFun.F.{u v} A :=
CoeToFun.coe

/- User level coercion operators -/

definition coe {A : Type u} {B : Type v} [LiftTrans A B] : A → B :=
@LiftTrans.lift A B _

definition coeFn {A : Type u} [CoeToFun.{u v} A] : A → CoeToFun.F.{u v} A :=
CoeToFun.coe

definition coeSort {A : Type u} [CoeToSort.{u v} A] : A → CoeToSort.S.{u v} A :=
CoeToSort.coe

/- Notation -/

notation `↑`:max a:max := coe a

notation `⇑`:max a:max := coeFn a

notation `↥`:max a:max := coeSort a

/- Transitive closure for has_lift, has_coe, has_coe_to_fun -/

attribute [instance]
definition {u₁ u₂ u₃} liftTrans {A : Type u₁} {B : Type u₂} {C : Type u₃} [Lift A B] [LiftTrans B C] : LiftTrans A C :=
⟨λ a, coe (lift a : B)⟩

attribute [instance]
definition liftBase {A : Type u} {B : Type v} [Lift A B] : LiftTrans A B :=
⟨lift⟩

attribute [instance]
definition {u₁ u₂ u₃} coeTrans {A : Type u₁} {B : Type u₂} {C : Type u₃} [Coe A B] [CoeTrans B C] : CoeTrans A C :=
⟨λ a, CoeTrans.coe C (@Coe.coe A B _ a)⟩

attribute [instance]
definition coeBase {A : Type u} {B : Type v} [Coe A B] : CoeTrans A B :=
⟨@Coe.coe A B _⟩

attribute [instance]
definition {u₁ u₂ u₃} coeToFunTrans {A : Type u₁} {B : Type u₂} [LiftTrans A B] [CoeToFun.{u₂ u₃} B] : CoeToFun.{u₁ u₃} A :=
⟨CoeToFun.F B, λ a, coeFn (coe a)⟩

attribute [instance]
definition {u₁ u₂ u₃} coeToSortTrans {A : Type u₁} {B : Type u₂} [LiftTrans A B] [CoeToSort.{u₂ u₃} B] : CoeToSort.{u₁ u₃} A :=
⟨CoeToSort.S B, λ a, coeSort (coe a)⟩

/- Every coercion is also a lift -/

attribute [instance]
definition coeToLift {A : Type u} {B : Type v} [CoeTrans A B] : LiftTrans A B :=
⟨@CoeTrans.coe A B _⟩

/- Basic coercions -/

attribute [instance]
definition coeBoolProp : Coe Bool Prop :=
⟨λ b, b = tt⟩

attribute [instance]
definition decidableCoeEq (b : Bool) : Decidable (coe b) :=
show Decidable (b = tt), from decidableEqBool b tt

attribute [instance]
definition coeSubtype {A : Type u} {P : A → Prop} : Coe {a \ P a} A :=
⟨λ s, Subtype.elt_of s⟩

/- Basic lifts -/

/- Remark: we can't use [has_lift_t A₂ A₁] since it will produce non-termination whenever a type class resolution
   problem does not have a solution. -/
attribute [instance]
definition {ua₁ ua₂ ub₁ ub₂} liftFn {A₁ : Type ua₁} {A₂ : Type ua₂} {B₁ : Type ub₁} {B₂ : Type ub₂} [Lift A₂ A₁] [LiftTrans B₁ B₂] : Lift (A₁ → B₁) (A₂ → B₂) :=
⟨λ f a, ↑(f ↑a)⟩

attribute [instance]
definition {ua ub₁ ub₂} liftRange {A : Type ua} {B₁ : Type ub₁} {B₂ : Type ub₂} [LiftTrans B₁ B₂] : Lift (A → B₁) (A → B₂) :=
⟨λ f a, ↑(f a)⟩

attribute [instance]
definition {ua₁ ua₂ ub} liftDomain {A₁ : Type ua₁} {A₂ : Type ua₂} {B : Type ub} [Lift A₂ A₁] : Lift (A₁ → B) (A₂ → B) :=
⟨λ f a, f ↑a⟩

attribute [instance]
definition {ua₁ ua₂ ub₁ ub₂} liftPair {A₁ : Type ua₁} {A₂ : Type ub₂} {B₁ : Type ub₁} {B₂ : Type ub₂} [LiftTrans A₁ A₂] [LiftTrans B₁ B₂] : Lift (A₁ × B₁) (A₂ × B₂) :=
⟨λ p, Prod.cases_on p (λ a b, (↑a, ↑b))⟩

attribute [instance]
definition {ua₁ ua₂ ub} liftPairLeft {A₁ : Type ua₁} {A₂ : Type ua₂} {B : Type ub} [LiftTrans A₁ A₂] : Lift (A₁ × B) (A₂ × B) :=
⟨λ p, Prod.cases_on p (λ a b, (↑a, b))⟩

attribute [instance]
definition {ua ub₁ ub₂} liftPairRight {A : Type ua} {B₁ : Type ub₁} {B₂ : Type ub₂} [LiftTrans B₁ B₂] : Lift (A × B₁) (A × B₂) :=
⟨λ p, Prod.cases_on p (λ a b, (a, ↑b))⟩

attribute [instance]
definition lift_li {A : Type u} {B : Type v} [LiftTrans A B] : Lift (List A) (List B) :=
⟨λ l, List.map (@coe A B _) l⟩
