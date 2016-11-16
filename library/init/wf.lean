/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.relation init.nat init.prod

universe variables u v

inductive acc {A : Type u} (r : A → A → Prop) : A → Prop
| intro : ∀ x, (∀ y, r y x → acc y) → acc x

namespace acc
  variables {A : Type u} {r : A → A → Prop}

  def inv {x y : A} (h₁ : acc r x) (h₂ : r y x) : acc r y :=
  acc.rec_on h₁ (λ x₁ ac₁ ih h₂, ac₁ y h₂) h₂

  -- dependent elimination for acc
  attribute [recursor]
  protected def drec
      {C : Π (a : A), acc r a → Type v}
      (h₁ : Π (x : A) (acx : Π (y : A), r y x → acc r y), (Π (y : A) (ryx : r y x), C y (acx y ryx)) → C x (acc.intro x acx))
      {a : A} (h₂ : acc r a) : C a h₂ :=
  acc.rec (λ x acx ih h₂, h₁ x acx (λ y ryx, ih y ryx (acx y ryx))) h₂ h₂
end acc

inductive well_founded {A : Type u} (r : A → A → Prop) : Prop
| intro : (∀ a, acc r a) → well_founded

namespace well_founded
  def apply {A : Type u} {r : A → A → Prop} (wf : well_founded r) : ∀ a, acc r a :=
  take a, well_founded.rec_on wf (λ p, p) a

  section
  parameters {A : Type u} {r : A → A → Prop}
  local infix `≺`:50    := r

  hypothesis hwf : well_founded r

  lemma recursion {C : A → Type v} (a : A) (h : Π x, (Π y, y ≺ x → C y) → C x) : C a :=
  acc.rec_on (apply hwf a) (λ x₁ ac₁ ih, h x₁ ih)

  lemma induction {C : A → Prop} (a : A) (h : ∀ x, (∀ y, y ≺ x → C y) → C x) : C a :=
  recursion a h

  variable {C : A → Type v}
  variable F : Π x, (Π y, y ≺ x → C y) → C x

  def fix_F (x : A) (a : acc r x) : C x :=
  acc.rec_on a (λ x₁ ac₁ ih, F x₁ ih)

  lemma fix_F_eq (x : A) (r : acc r x) :
    fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)) :=
  acc.drec (λ x r ih, rfl) r
  end

  variables {A : Type u} {C : A → Type v} {r : A → A → Prop}

  -- Well-founded fixpoint
  def fix (hwf : well_founded r) (F : Π x, (Π y, r y x → C y) → C x) (x : A) : C x :=
  fix_F F x (apply hwf x)

  -- Well-founded FO fixpoint
  definition fixFO {B : Type} [Hwf : well_founded R] (F : Π x, (Π y, R y x -> B) -> B) (x : A) : B :=
    @fix A (fun a, B) R Hwf F x

  -- Well-founded fixpoint satisfies fixpoint equation
  lemma fix_eq (hwf : well_founded r) (F : Π x, (Π y, r y x → C y) → C x) (x : A) :
    fix hwf F x = F x (λ y h, fix hwf F y) :=
  fix_F_eq F x (apply hwf x)
end well_founded

open well_founded

-- Empty relation is well-founded
def empty_wf {A : Type u} : well_founded empty_relation :=
well_founded.intro (λ (a : A),
  acc.intro a (λ (b : A) (lt : false), false.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
section
  parameters {A : Type u} {r Q : A → A → Prop}
  parameters (h₁ : subrelation Q r)
  parameters (h₂ : well_founded r)

  def accessible {a : A} (ac : acc r a) : acc Q a :=
  acc.rec_on ac (λ x ax ih,
    acc.intro x (λ (y : A) (lt : Q y x), ih y (h₁ lt)))

  def wf : well_founded Q :=
  ⟨λ a, accessible (apply h₂ a)⟩
end
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace inv_image
section
  parameters {A : Type u} {B : Type v} {r : B → B → Prop}
  parameters (f : A → B)
  parameters (h : well_founded r)

  private def acc_aux {b : B} (ac : acc r b) : ∀ (x : A), f x = b → acc (inv_image r f) x :=
  acc.rec_on ac (λ x acx ih z e,
    acc.intro z (λ y lt, eq.rec_on e (λ acx ih, ih (f y) lt y rfl) acx ih))

  def accessible {a : A} (ac : acc r (f a)) : acc (inv_image r f) a :=
  acc_aux ac a rfl

  def wf : well_founded (inv_image r f) :=
  ⟨λ a, accessible (apply h (f a))⟩
end
end inv_image

-- The transitive closure of a well-founded relation is well-founded
namespace tc
section
  parameters {A : Type u} {r : A → A → Prop}
  local notation `r⁺` := tc r

  def accessible {z : A} (ac : acc r z) : acc (tc r) z :=
  acc.rec_on ac (λ x acx ih,
    acc.intro x (λ y rel,
      tc.rec_on rel
        (λ a b rab acx ih, ih a rab)
        (λ a b c rab rbc ih₁ ih₂ acx ih, acc.inv (ih₂ acx ih) rab)
        acx ih))

  def wf (h : well_founded r) : well_founded r⁺ :=
  ⟨λ a, accessible (apply h a)⟩
end
end tc

-- less-than is well-founded
def nat.lt_wf : well_founded nat.lt :=
⟨nat.rec
  (acc.intro 0 (λ n h, absurd h (nat.not_lt_zero n)))
  (λ n ih, acc.intro (nat.succ n) (λ m h,
     or.elim (nat.eq_or_lt_of_le (nat.le_of_succ_le_succ h))
        (λ e, eq.substr e ih) (acc.inv ih)))⟩

def measure {A : Type u} : (A → ℕ) → A → A → Prop :=
inv_image lt

def measure_wf {A : Type u} (f : A → ℕ) : well_founded (measure f) :=
inv_image.wf f nat.lt_wf

namespace prod
  open well_founded

  section
  variables {A : Type u} {B : Type v}
  variable  (ra  : A → A → Prop)
  variable  (rb  : B → B → Prop)

  -- Lexicographical order based on ra and rb
  inductive lex : A × B → A × B → Prop
  | left  : ∀ {a₁ b₁} a₂ b₂, ra a₁ a₂ → lex (a₁, b₁) (a₂, b₂)
  | right : ∀ a {b₁ b₂},     rb b₁ b₂ → lex (a, b₁)  (a, b₂)

  -- relational product based on ra and rb
  inductive rprod : A × B → A × B → Prop
  | intro : ∀ {a₁ b₁ a₂ b₂}, ra a₁ a₂ → rb b₁ b₂ → rprod (a₁, b₁) (a₂, b₂)
  end

  section
  parameters {A : Type u} {B : Type v}
  parameters {ra  : A → A → Prop} {rb  : B → B → Prop}
  local infix `≺`:50 := lex ra rb

  def lex_accessible {a} (aca : acc ra a) (acb : ∀ b, acc rb b): ∀ b, acc (lex ra rb) (a, b) :=
  acc.rec_on aca (λ xa aca iha b,
    acc.rec_on (acb b) (λ xb acb ihb,
      acc.intro (xa, xb) (λ p lt,
        have aux : xa = xa → xb = xb → acc (lex ra rb) p, from
          @prod.lex.rec_on A B ra rb (λ p₁ p₂, fst p₂ = xa → snd p₂ = xb → acc (lex ra rb) p₁)
                           p (xa, xb) lt
            (λ a₁ b₁ a₂ b₂ h (eq₂ : a₂ = xa) (eq₃ : b₂ = xb), iha a₁ (eq.rec_on eq₂ h) b₁)
            (λ a b₁ b₂ h (eq₂ : a = xa) (eq₃ : b₂ = xb), eq.rec_on eq₂~>symm (ihb b₁ (eq.rec_on eq₃ h))),
        aux rfl rfl)))

  -- The lexicographical order of well founded relations is well-founded
  def lex_wf (ha : well_founded ra) (hb : well_founded rb) : well_founded (lex ra rb) :=
  ⟨λ p, destruct p (λ a b, lex_accessible (apply ha a) (well_founded.apply hb) b)⟩

  -- relational product is a subrelation of the lex
  def rprod_sub_lex : ∀ a b, rprod ra rb a b → lex ra rb a b :=
  λ a b h, prod.rprod.rec_on h (λ a₁ b₁ a₂ b₂ h₁ h₂, lex.left rb a₂ b₂ h₁)

  -- The relational product of well founded relations is well-founded
  def rprod_wf (ha : well_founded ra) (hb : well_founded rb) : well_founded (rprod ra rb) :=
  subrelation.wf (rprod_sub_lex) (lex_wf ha hb)

  end

end prod
