/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.relation init.nat init.prod

universe variables u v

inductive acc {A : Type u} (r : A → A → Prop) : A → Prop
| intro : ∀x, (∀ y, r y x → acc y) → acc x

namespace acc
  variables {A : Type u} {r : A → A → Prop}

  definition inv {x y : A} (H₁ : acc r x) (H₂ : r y x) : acc r y :=
  acc.rec_on H₁ (λ x₁ ac₁ iH H₂, ac₁ y H₂) H₂

  -- dependent elimination for acc
  attribute [recursor]
  protected definition drec
      {C : Π (a : A), acc r a → Type v}
      (h₁ : Π (x : A) (acx : Π (y : A), r y x → acc r y),
              (Π (y : A) (ryx : r y x), C y (acx y ryx)) → C x (acc.intro x acx))
      {a : A} (h₂ : acc r a) : C a h₂ :=
  @acc.rec _ _ (λ (a : A), Π (x : @acc A r a), C a x)
    (λ x acx ih h₂, h₁ x acx (λ y ryx, ih y ryx (acx y ryx)))
    _
    h₂
    h₂
end acc

inductive well_founded {A : Type u} (r : A → A → Prop) : Prop
| intro : (∀ a, acc r a) → well_founded

namespace well_founded
  definition apply {A : Type u} {r : A → A → Prop} (wf : well_founded r) : ∀ a, acc r a :=
  take a, well_founded.rec_on wf (λp, p) a

  section
  parameters {A : Type u} {r : A → A → Prop}
  local infix `≺`:50    := r

  hypothesis Hwf : well_founded r

  theorem recursion {C : A → Type v} (a : A) (H : Πx, (Πy, y ≺ x → C y) → C x) : C a :=
  acc.rec_on (apply Hwf a) (λ x₁ ac₁ iH, H x₁ iH)

  theorem induction {C : A → Prop} (a : A) (H : ∀x, (∀y, y ≺ x → C y) → C x) : C a :=
  recursion a H

  variable {C : A → Type v}
  variable F : Πx, (Πy, y ≺ x → C y) → C x

  definition fix_F (x : A) (a : acc r x) : C x :=
  acc.rec_on a (λ x₁ ac₁ iH, F x₁ iH)

  theorem fix_F_eq (x : A) (r : acc r x) :
    fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)) :=
  acc.drec (λ x r ih, rfl) r
  end

  variables {A : Type u} {C : A → Type v} {r : A → A → Prop}

  -- Well-founded fixpoint
  definition fix (Hwf : well_founded r) (F : Πx, (Πy, r y x → C y) → C x) (x : A) : C x :=
  fix_F F x (apply Hwf x)

  -- Well-founded fixpoint satisfies fixpoint equation
  theorem fix_eq (Hwf : well_founded r) (F : Πx, (Πy, r y x → C y) → C x) (x : A) :
    fix Hwf F x = F x (λy h, fix Hwf F y) :=
  fix_F_eq F x (apply Hwf x)
end well_founded

open well_founded

-- Empty relation is well-founded
definition empty_wf {A : Type u} : well_founded empty_relation :=
well_founded.intro (λ (a : A),
  acc.intro a (λ (b : A) (lt : false), false.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
section
  parameters {A : Type u} {r Q : A → A → Prop}
  parameters (H₁ : subrelation Q r)
  parameters (H₂ : well_founded r)

  definition accessible {a : A} (ac : acc r a) : acc Q a :=
  acc.rec_on ac (λ x ax ih,
    acc.intro x (λ (y : A) (lt : Q y x), ih y (H₁ lt)))

  definition wf : well_founded Q :=
  well_founded.intro (λ a, accessible (apply H₂ a))
end
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace inv_image
section
  parameters {A : Type u} {B : Type v} {r : B → B → Prop}
  parameters (f : A → B)
  parameters (H : well_founded r)

  private definition acc_aux : ∀ {b : B}, @acc B r b → (∀ (x : A), @eq B (f x) b → @acc A (@inv_image A B r f) x) :=
  @acc.rec B r (λ (b : B), ∀ (x : A), f x = b → acc (inv_image r f) x)
    (λ (x : B)
       (acx : ∀ (y : B), r y x → acc r y)
       (ih : ∀ (y : B), r y x → (λ (b : B), ∀ (x : A), f x = b → acc (inv_image r f) x) y)
       (z : A) (e : f z = x),
       acc.intro z
         (λ (y : A) (lt : inv_image r f y z),
            @eq.rec B (f z)
              (λ (x : B),
                 (∀ (y : B), r y x → acc r y) →
                 (∀ (y : B), r y x → (λ (b : B), ∀ (x : A), f x = b → acc (inv_image r f) x) y) → acc (inv_image r f) y)
              (λ (acx : ∀ (y : B), r y (f z) → @acc B r y)
                 (ih :  ∀ (y : B), r y (f z) → (λ (b : B), ∀ (x : A), f x = b → acc (inv_image r f) x) y),
                 ih (f y) lt y (@rfl B (f y)))
              x
              e
              acx
              ih))

  definition accessible {a : A} (ac : acc r (f a)) : acc (inv_image r f) a :=
  acc_aux ac a rfl

  definition wf : well_founded (inv_image r f) :=
  well_founded.intro (λ a, accessible (apply H (f a)))
end
end inv_image

-- The transitive closure of a well-founded relation is well-founded
namespace tc
section
  parameters {A : Type u} {r : A → A → Prop}
  local notation `r⁺` := tc r

  definition accessible : ∀ {z : A}, acc r z → acc (tc r) z :=
  @acc.rec A r (acc (tc r))
    (λ (x : A) (acx : ∀ (y : A), r y x → acc r y) (ih : ∀ (y : A), r y x → acc (tc r) y),
       @acc.intro A (tc r) x
         (λ (y : A) (rel : tc r y x),
            @tc.rec A r
              (λ (y x : A),
                 (∀ (y : A), r y x → acc r y) →
                 (∀ (y : A), r y x → acc (tc r) y) → acc (tc r) y)
              (λ (a b : A) (rab : r a b) (acx : ∀ (y : A), r y b → acc r y)
                 (ih : ∀ (y : A), r y b → acc (tc r) y),
                 ih a rab)
              (λ (a b c : A) (rab : tc r a b) (rbc : tc r b c)
                 (ih₁ : (∀ (y : A), r y b → acc r y) → (∀ (y : A), r y b → acc (tc r) y) → acc (tc r) a)
                 (ih₂ : (∀ (y : A), r y c → acc r y) → (∀ (y : A), r y c → acc (tc r) y) → acc (tc r) b)
                 (acx : ∀ (y : A), r y c → acc r y) (ih : ∀ (y : A), r y c → acc (tc r) y),
                 @acc.inv A (@tc A r) b a (ih₂ acx ih) rab)
              y
              x
              rel
              acx
              ih))

  definition wf (H : well_founded r) : well_founded r⁺ :=
  well_founded.intro (λ a, accessible (apply H a))
end
end tc

-- less-than is well-founded
definition Nat.lt_wf : well_founded Nat.lt :=
well_founded.intro (Nat.rec
  (acc.intro 0 (λn H, absurd H (Nat.not_lt_zero n)))
  (λn ih, acc.intro (Nat.succ n) (λm H,
     or_elim (Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ H))
        (λe, eq_substr e ih) (acc.inv ih))))

definition measure {A : Type u} : (A → ℕ) → A → A → Prop :=
inv_image lt

definition measure_wf {A : Type u} (f : A → ℕ) : well_founded (measure f) :=
inv_image.wf f Nat.lt_wf

namespace Prod
  open well_founded

  section
  variables {A : Type u} {B : Type v}
  variable  (ra  : A → A → Prop)
  variable  (rb  : B → B → Prop)

  -- Lexicographical order based on ra and rb
  inductive lex : A × B → A × B → Prop
  | left  : ∀{a₁ b₁} a₂ b₂, ra a₁ a₂ → lex (a₁, b₁) (a₂, b₂)
  | right : ∀a {b₁ b₂},     rb b₁ b₂ → lex (a, b₁)  (a, b₂)

  -- relational product based on ra and rb
  inductive rprod : A × B → A × B → Prop
  | intro : ∀{a₁ b₁ a₂ b₂}, ra a₁ a₂ → rb b₁ b₂ → rprod (a₁, b₁) (a₂, b₂)
  end

  section
  parameters {A : Type u} {B : Type v}
  parameters {ra  : A → A → Prop} {rb  : B → B → Prop}
  local infix `≺`:50 := lex ra rb

  definition lex_accessible {a} (aca : acc ra a) (acb : ∀b, acc rb b): ∀b, acc (lex ra rb) (a, b) :=
  acc.rec_on aca
    (λxa aca (iHa : ∀y, ra y xa → ∀b, acc (lex ra rb) (y, b)),
      λb, acc.rec_on (acb b)
        (λxb acb
          (iHb : ∀y, rb y xb → acc (lex ra rb) (xa, y)),
          acc.intro (xa, xb) (λp (lt : p ≺ (xa, xb)),
            have aux : xa = xa → xb = xb → acc (lex ra rb) p, from
              @Prod.lex.rec_on A B ra rb (λp₁ p₂, pr₁ p₂ = xa → pr₂ p₂ = xb → acc (lex ra rb) p₁)
                               p (xa, xb) lt
                (λa₁ b₁ a₂ b₂ (H : ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
                  show acc (lex ra rb) (a₁, b₁), from
                  have ra₁  : ra a₁ xa, from eq.rec_on eq₂ H,
                  iHa a₁ ra₁ b₁)
                (λa b₁ b₂ (H : rb b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ = xb),
                  show acc (lex ra rb) (a, b₁), from
                  have rb₁  : rb b₁ xb, from eq.rec_on eq₃ H,
                  have eq₂' : xa = a, from eq.rec_on eq₂ rfl,
                  eq.rec_on eq₂' (iHb b₁ rb₁)),
            aux rfl rfl)))

  -- The lexicographical order of well founded relations is well-founded
  definition lex_wf (Ha : well_founded ra) (Hb : well_founded rb) : well_founded (lex ra rb) :=
  well_founded.intro (λp, destruct p (λa b, lex_accessible (apply Ha a) (well_founded.apply Hb) b))

  -- relational product is a subrelation of the lex
  definition rprod_sub_lex : ∀ a b, rprod ra rb a b → lex ra rb a b :=
  λa b H, Prod.rprod.rec_on H (λ a₁ b₁ a₂ b₂ H₁ H₂, lex.left rb a₂ b₂ H₁)

  -- The relational product of well founded relations is well-founded
  definition rprod_wf (Ha : well_founded ra) (Hb : well_founded rb) : well_founded (rprod ra rb) :=
  subrelation.wf (rprod_sub_lex) (lex_wf Ha Hb)

  end

end Prod
