/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Basic datatypes
-/
prelude

notation `Prop`  := Type 0
notation `Type₂` := Type 2
notation `Type₃` := Type 3

universe variables u v

inductive PolyUnit : Type u
| star : PolyUnit

inductive Unit : Type
| star : Unit

inductive true : Prop
| intro : true

inductive false : Prop

inductive Empty : Type

inductive eq {A : Type u} (a : A) : A → Prop
| refl : eq a

inductive heq {A : Type u} (a : A) : Π {B : Type u}, B → Prop
| refl : heq a

structure Prod (A : Type u) (B : Type v) :=
(pr1 : A) (pr2 : B)

inductive and (a b : Prop) : Prop
| intro : a → b → and

definition and_elim_left {a b : Prop} (H : and a b) : a :=
and.rec (λ Ha Hb, Ha) H

definition and_left := @and_elim_left

definition and_elim_right {a b : Prop} (H : and a b) : b :=
and.rec (λ Ha Hb, Hb) H

definition and_right := @and_elim_right

inductive Sum (A : Type u) (B : Type v)
| inl {} : A → Sum
| inr {} : B → Sum

attribute [reducible]
definition Sum.intro_left {A : Type u} (B : Type v) (a : A) : Sum A B :=
Sum.inl a

attribute [reducible]
definition Sum.intro_right (A : Type u) {B : Type v} (b : B) : Sum A B :=
Sum.inr b

inductive or (a b : Prop) : Prop
| inl {} : a → or
| inr {} : b → or

structure Sigma {A : Type u} (B : A → Type v) :=
mk :: (pr1 : A) (pr2 : B pr1)

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26.
-- The parser will generate the terms (pos (bit1 (bit1 (bit0 one)))), zero, and (pos (bit0 (bit1 (bit1 one)))).
-- This representation can be coerced in whatever we want (e.g., naturals, integers, reals, etc).
inductive PosNum : Type
| one  : PosNum
| bit1 : PosNum → PosNum
| bit0 : PosNum → PosNum

definition PosNum.succ (a : PosNum) : PosNum :=
PosNum.rec_on a (PosNum.bit0 PosNum.one) (λn r, PosNum.bit0 r) (λn r, PosNum.bit1 n)

inductive Num : Type
| zero  : Num
| pos   : PosNum → Num

definition Num.succ (a : Num) : Num :=
Num.rec_on a (Num.pos PosNum.one) (λp, Num.pos (PosNum.succ p))

inductive Bool : Type
| ff : Bool
| tt : Bool

inductive Option (A : Type u)
| none {} : Option
| some    : A → Option

export Option (none some)
export Bool (ff tt)

inductive List (T : Type u)
| nil {} : List
| cons   : T → List → List

inductive Nat
| zero : Nat
| succ : Nat → Nat

/- Declare builtin and reserved notation -/

notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r

structure [class] Zero    (A : Type u) := (zero : A)
structure [class] One     (A : Type u) := (one : A)
structure [class] Add     (A : Type u) := (add : A → A → A)
structure [class] Mul     (A : Type u) := (mul : A → A → A)
structure [class] Inv     (A : Type u) := (inv : A → A)
structure [class] Neg     (A : Type u) := (neg : A → A)
structure [class] Sub     (A : Type u) := (sub : A → A → A)
structure [class] Div     (A : Type u) := (div : A → A → A)
structure [class] Dvd     (A : Type u) := (dvd : A → A → Prop)
structure [class] Mod     (A : Type u) := (mod : A → A → A)
structure [class] Le      (A : Type u) := (le : A → A → Prop)
structure [class] Lt      (A : Type u) := (lt : A → A → Prop)
structure [class] Append  (A : Type u) := (append : A → A → A)
structure [class] AndThen (A : Type u) := (andThen : A → A → A)

definition zero    {A : Type u} [Zero A]    : A            := Zero.zero A
definition one     {A : Type u} [One A]     : A            := One.one A
definition add     {A : Type u} [Add A]     : A → A → A    := Add.add
definition mul     {A : Type u} [Mul A]     : A → A → A    := Mul.mul
definition sub     {A : Type u} [Sub A]     : A → A → A    := Sub.sub
definition div     {A : Type u} [Div A]     : A → A → A    := Div.div
definition dvd     {A : Type u} [Dvd A]     : A → A → Prop := Dvd.dvd
definition mod     {A : Type u} [Mod A]     : A → A → A    := Mod.mod
definition neg     {A : Type u} [Neg A]     : A → A        := Neg.neg
definition inv     {A : Type u} [Inv A]     : A → A        := Inv.inv
definition le      {A : Type u} [Le A]      : A → A → Prop := Le.le
definition lt      {A : Type u} [Lt A]      : A → A → Prop := Lt.lt
definition append  {A : Type u} [Append A]  : A → A → A    := Append.append
definition andthen {A : Type u} [AndThen A] : A → A → A    := AndThen.andThen

attribute [reducible]
definition ge {A : Type u} [s : Le A] (a b : A) : Prop := le b a
attribute [reducible]
definition gt {A : Type u} [s : Lt A] (a b : A) : Prop := lt b a
definition bit0 {A : Type u} [s  : Add A] (a  : A)             : A := add a a
definition bit1 {A : Type u} [s₁ : One A] [s₂ : Add A] (a : A) : A := add (bit0 a) one

attribute [pattern] zero one bit0 bit1 add

attribute [instance]
definition zeroNum : Zero Num :=
⟨Num.zero⟩

attribute [instance]
definition oneNum : One Num :=
⟨Num.pos PosNum.one⟩

attribute [instance]
definition onePosNum : One PosNum :=
⟨PosNum.one⟩

namespace PosNum
  definition is_one (a : PosNum) : Bool :=
  PosNum.rec_on a tt (λn r, ff) (λn r, ff)

  definition pred (a : PosNum) : PosNum :=
  PosNum.rec_on a one (λn r, bit0 n) (λn r, Bool.rec_on (is_one n) (bit1 r) one)

  definition size (a : PosNum) : PosNum :=
  PosNum.rec_on a one (λn r, succ r) (λn r, succ r)

  definition add (a b : PosNum) : PosNum :=
  PosNum.rec_on a
    succ
    (λn f b, PosNum.rec_on b
      (succ (bit1 n))
      (λm r, succ (bit1 (f m)))
      (λm r, bit1 (f m)))
    (λn f b, PosNum.rec_on b
      (bit1 n)
      (λm r, bit1 (f m))
      (λm r, bit0 (f m)))
    b
end PosNum

attribute [instance]
definition addPosNum : Add PosNum :=
⟨PosNum.add⟩

namespace Num
  open PosNum

  definition add (a b : Num) : Num :=
  Num.rec_on a b (λpa, Num.rec_on b (pos pa) (λpb, pos (PosNum.add pa pb)))
end Num

attribute [instance]
definition addNum : Add Num :=
⟨Num.add⟩

definition std.priority.default : Num := 1000
definition std.priority.max     : Num := 4294967295

protected definition Nat.prio := Num.add std.priority.default 100

protected definition Nat.add (a b : Nat) : Nat :=
Nat.rec a (λ b₁ r, Nat.succ r) b

definition Nat.ofPosNum (p : PosNum) : Nat :=
PosNum.rec (Nat.succ Nat.zero) (λ n r, Nat.add (Nat.add r r) (Nat.succ Nat.zero)) (λ n r, Nat.add r r) p

definition Nat.ofNum (n : Num) : Nat :=
Num.rec Nat.zero (λ p, Nat.ofPosNum p) n

attribute [instance, priority Nat.prio] addPosNum onePosNum zeroNum oneNum addNum

attribute [instance, priority Nat.prio]
definition zeroNat : Zero Nat :=
⟨Nat.zero⟩

attribute [instance, priority Nat.prio]
definition oneNat : One Nat :=
⟨Nat.succ Nat.zero⟩

attribute [instance, priority Nat.prio]
definition addNat : Add Nat :=
⟨Nat.add⟩

/-
  Global declarations of right binding strength

  If a module reassigns these, it will be incompatible with other modules that adhere to these
  conventions.

  When hovering over a symbol, use "C-c C-k" to see how to input it.
-/
definition std.prec.max   : Num := 1024 -- the strength of application, identifiers, (, [, etc.
definition std.prec.arrow : Num := 25

/-
The next definition is "max + 10". It can be used e.g. for postfix operations that should
be stronger than application.
-/

definition std.prec.max_plus :=
Num.succ (Num.succ (Num.succ (Num.succ (Num.succ (Num.succ (Num.succ (Num.succ (Num.succ
  (Num.succ std.prec.max)))))))))

/- Logical operations and relations -/

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr ` ∧ `:35
reserve infixr ` /\ `:35
reserve infixr ` \/ `:30
reserve infixr ` ∨ `:30
reserve infix ` <-> `:20
reserve infix ` ↔ `:20
reserve infix ` = `:50
reserve infix ` ≠ `:50
reserve infix ` ≈ `:50
reserve infix ` ~ `:50
reserve infix ` ≡ `:50

reserve infixl ` ⬝ `:75
reserve infixr ` ▸ `:75
reserve infixr ` ▹ `:75

/- types and type constructors -/

reserve infixr ` ⊕ `:30
reserve infixr ` × `:35

/- arithmetic operations -/

reserve infixl ` + `:65
reserve infixl ` - `:65
reserve infixl ` * `:70
reserve infixl ` / `:70
reserve infixl ` % `:70
reserve prefix `-`:100
reserve infix ` ^ `:80

reserve infixr ` ∘ `:90                 -- input with \comp
reserve postfix `⁻¹`:std.prec.max_plus  -- input with \sy or \-1 or \inv

reserve infix ` <= `:50
reserve infix ` ≤ `:50
reserve infix ` < `:50
reserve infix ` >= `:50
reserve infix ` ≥ `:50
reserve infix ` > `:50

/- boolean operations -/

reserve infixl ` && `:70
reserve infixl ` || `:65

/- set operations -/

reserve infix ` ∈ `:50
reserve infix ` ∉ `:50
reserve infixl ` ∩ `:70
reserve infixl ` ∪ `:65
reserve infix ` ⊆ `:50
reserve infix ` ⊇ `:50
reserve infix ` ' `:75   -- for the image of a set under a function
reserve infix ` '- `:75  -- for the preimage of a set under a function

/- other symbols -/

reserve infix ` ∣ `:50
reserve infixl ` ++ `:65
reserve infixr ` :: `:67
reserve infixl `; `:1

infix +    := add
infix *    := mul
infix -    := sub
infix /    := div
infix ∣    := dvd
infix %    := mod
prefix -   := neg
postfix ⁻¹ := inv
infix <=   := le
infix >=   := ge
infix ≤    := le
infix ≥    := ge
infix <    := lt
infix >    := gt
infix ++   := append
infix ;    := andthen

/- eq basic support -/
notation a = b := eq a b

attribute [refl] eq.refl

attribute [pattern]
definition rfl {A : Type u} {a : A} : a = a := eq.refl a

attribute [elab_as_eliminator, subst]
theorem eq.subst {A : Type u} {P : A → Prop} {a b : A} (H₁ : a = b) (H₂ : P a) : P b :=
eq.rec H₂ H₁

attribute [trans]
theorem eq_trans {A : Type u} {a b c: A} (H₁ : a = b) (H₂ : b = c) : a = c :=
eq.subst H₂ H₁

attribute [symm]
theorem eq_symm {A : Type u} {a b : A} : a = b → b = a :=
λ h, eq.rec (eq.refl a) h

notation H1 ▸ H2 := eq.subst H1 H2

/- sizeof -/

structure [class] Sizeof (A : Type u) :=
(sizeof : A → Nat)

definition sizeof {A : Type u} [s : Sizeof A] : A → Nat :=
Sizeof.sizeof

/-
Declare sizeof instances and lemmas for types declared before Sizeof.
From now on, the inductive compiler will automatically generate sizeof instances and lemmas.
-/

/- Every type `A` has a default Sizeof instance that just returns 0 for every element of `A` -/
attribute [instance]
definition defaultSizeof (A : Type u) : Sizeof A :=
⟨λ a, Nat.zero⟩

attribute [simp, defeq, simp.sizeof]
definition defaultSizeof_eq (A : Type u) (a : A) : @sizeof A (defaultSizeof A) a = 0 :=
rfl

attribute [instance]
definition sizeofNat : Sizeof Nat :=
⟨λ a, a⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofNat_eq (a : Nat) : sizeof a = a :=
rfl

attribute [instance]
definition sizeofProf (A : Type u) (B : Type v) [Sizeof A] [Sizeof B] : Sizeof (Prod A B) :=
⟨λ p, Prod.cases_on p (λ a b, 1 + sizeof a + sizeof b)⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofProd_eq {A : Type u} {B : Type v} [Sizeof A] [Sizeof B] (a : A) (b : B) : sizeof (Prod.mk a b) = 1 + sizeof a + sizeof b :=
rfl

attribute [instance]
definition sizeofSum (A : Type u) (B : Type v) [Sizeof A] [Sizeof B] : Sizeof (Sum A B) :=
⟨λ s, Sum.cases_on s (λ a, 1 + sizeof a) (λ b, 1 + sizeof b)⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofSum_eq_left {A : Type u} {B : Type v} [Sizeof A] [Sizeof B] (a : A) : sizeof (@Sum.inl A B a) = 1 + sizeof a :=
rfl

attribute [simp, defeq, simp.sizeof]
definition sizeofSum_eq_right {A : Type u} {B : Type v} [Sizeof A] [Sizeof B] (b : B) : sizeof (@Sum.inr A B b) = 1 + sizeof b :=
rfl

attribute [instance]
definition sizeofSigma (A : Type u) (B : A → Type v) [Sizeof A] [∀ a, Sizeof (B a)] : Sizeof (Sigma B) :=
⟨λ p, Sigma.cases_on p (λ a b, 1 + sizeof a + sizeof b)⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofSigma_eq {A : Type u} {B : A → Type v} [Sizeof A] [∀ a, Sizeof (B a)] (a : A) (b : B a) : sizeof (@Sigma.mk A B a b) = 1 + sizeof a + sizeof b :=
rfl

attribute [instance]
definition sizeofUnit : Sizeof Unit :=
⟨λ u, 1⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofUnit_eq (u : Unit) : sizeof u = 1 :=
rfl

attribute [instance]
definition sizeofPolyUnit : Sizeof PolyUnit :=
⟨λ u, 1⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofPolyUnit_eq (u : PolyUnit) : sizeof u = 1 :=
rfl

attribute [instance]
definition sizeofBool : Sizeof Bool :=
⟨λ u, 1⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofBool_eq (b : Bool) : sizeof b = 1 :=
rfl

attribute [instance]
definition sizeofPosNum : Sizeof PosNum :=
⟨λ p, Nat.ofPosNum p⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofPosNum_eq (p : PosNum) : sizeof p = Nat.ofPosNum p :=
rfl

attribute [instance]
definition sizeofNum : Sizeof Num :=
⟨λ p, Nat.ofNum p⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofNum_eq (n : Num) : sizeof n = Nat.ofNum n :=
rfl

attribute [instance]
definition sizeofOption (A : Type u) [Sizeof A] : Sizeof (Option A) :=
⟨λ o, Option.cases_on o 1 (λ a, 1 + sizeof a)⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofOption_none_eq (A : Type u) [Sizeof A] : sizeof (@none A) = 1 :=
rfl

attribute [simp, defeq, simp.sizeof]
definition sizeofOption_some_eq {A : Type u} [Sizeof A] (a : A) : sizeof (some a) = 1 + sizeof a :=
rfl

attribute [instance]
definition sizeofList (A : Type u) [Sizeof A] : Sizeof (List A) :=
⟨λ l, List.rec_on l 1 (λ a t ih, 1 + sizeof a + ih)⟩

attribute [simp, defeq, simp.sizeof]
definition sizeofList_nil_eq (A : Type u) [Sizeof A] : sizeof (@List.nil A) = 1 :=
rfl

attribute [simp, defeq, simp.sizeof]
definition sizeofList_cons_eq {A : Type u} [Sizeof A] (a : A) (l : List A) : sizeof (List.cons a l) = 1 + sizeof a + sizeof l :=
rfl

attribute [simp.sizeof]
lemma nat_add_zero (n : Nat) : n + 0 = n := rfl
