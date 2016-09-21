/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Quotient types.
-/
prelude
import init.sigma init.setoid init.logic
open Sigma.ops

universe variables u v

constant Quot : Π {A : Type u}, Setoid A → Type u
-- Remark: if we do not use propext here, then we would need a quot.lift for propositions.
constant propext {a b : Prop} : (a ↔ b) → a = b

-- iff can now be used to do substitutions in a calculation
attribute [subst]
theorem iff_subst {a b : Prop} {p : Prop → Prop} (h₁ : a ↔ b) (h₂ : p a) : p b :=
eq.subst (propext h₁) h₂

namespace Quot
  protected constant mk        : Π {A : Type u}   [s : Setoid A], A → Quot s
  notation `⟦`:max a `⟧`:0 := Quot.mk a

  constant sound     : Π {A : Type u} [s : Setoid A] {a b : A}, a ≈ b → ⟦a⟧ = ⟦b⟧
  constant lift      : Π {A : Type u} {B : Type v} [s : Setoid A] (f : A → B), (∀ a b, a ≈ b → f a = f b) → Quot s → B
  constant ind       : ∀ {A : Type u} [s : Setoid A] {B : Quot s → Prop}, (∀ a, B ⟦a⟧) → ∀ q, B q

  attribute [elab_as_eliminator] lift ind

  init_quotient

  protected theorem lift_beta {A : Type u} {B : Type v} [Setoid A] (f : A → B) (c : ∀ a b, a ≈ b → f a = f b) (a : A) : lift f c ⟦a⟧ = f a :=
  rfl

  protected theorem ind_beta {A : Type u} [s : Setoid A] {B : Quot s → Prop} (p : ∀ a, B ⟦a⟧) (a : A) : (ind p ⟦a⟧ : B ⟦a⟧) = p a :=
  rfl

  attribute [reducible, elab_as_eliminator]
  protected definition lift_on {A : Type u} {B : Type v} [s : Setoid A] (q : Quot s) (f : A → B) (c : ∀ a b, a ≈ b → f a = f b) : B :=
  lift f c q

  attribute [elab_as_eliminator]
  protected theorem induction_on {A : Type u} [s : Setoid A] {B : Quot s → Prop} (q : Quot s) (H : ∀ a, B ⟦a⟧) : B q :=
  ind H q

  theorem exists_rep {A : Type u} [s : Setoid A] (q : Quot s) : ∃ a : A, ⟦a⟧ = q :=
  Quot.induction_on q (λ a, ⟨a, rfl⟩)

  section
  variable {A : Type u}
  variable [s : Setoid A]
  variable {B : Quot s → Type v}
  include s

  attribute [reducible]
  protected definition indep (f : Π a, B ⟦a⟧) (a : A) : Σ q, B q :=
  ⟨⟦a⟧, f a⟩

  protected lemma indep_coherent (f : Π a, B ⟦a⟧)
                       (H : ∀ (a b : A) (p : a ≈ b), (eq.rec (f a) (sound p) : B ⟦b⟧) = f b)
                       : ∀ a b, a ≈ b → Quot.indep f a = Quot.indep f b  :=
  λ a b e, Sigma.eq (sound e) (H a b e)

  protected lemma lift_indep_pr1
    (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), (eq.rec (f a) (sound p) : B ⟦b⟧) = f b)
    (q : Quot s) : (lift (Quot.indep f) (Quot.indep_coherent f H) q).1 = q  :=
  Quot.ind (λ (a : A), eq.refl (Quot.indep f a).1) q

  attribute [reducible, elab_as_eliminator]
  protected definition rec
     (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), (eq.rec (f a) (sound p) : B ⟦b⟧) = f b)
     (q : Quot s) : B q :=
  eq.rec_on (Quot.lift_indep_pr1 f H q) ((lift (Quot.indep f) (Quot.indep_coherent f H) q).2)

  attribute [reducible, elab_as_eliminator]
  protected definition rec_on
     (q : Quot s) (f : Π a, B ⟦a⟧) (H : ∀ (a b : A) (p : a ≈ b), (eq.rec (f a) (sound p) : B ⟦b⟧) = f b) : B q :=
  Quot.rec f H q

  attribute [reducible, elab_as_eliminator]
  protected definition rec_on_subsingleton
     [H : ∀ a, subsingleton (B ⟦a⟧)] (q : Quot s) (f : Π a, B ⟦a⟧) : B q :=
  Quot.rec f (λ a b h, subsingleton_elim _ (f b)) q

  attribute [reducible, elab_as_eliminator]
  protected definition hrec_on
     (q : Quot s) (f : Π a, B ⟦a⟧) (c : ∀ (a b : A) (p : a ≈ b), f a == f b) : B q :=
  Quot.rec_on q f
    (λ a b p, eq_of_heq (calc
      (eq.rec (f a) (sound p) : B ⟦b⟧) == f a : eq_rec_heq (sound p) (f a)
                                   ... == f b : c a b p))
  end

  section
  universe variables u_a u_b u_c
  variables {A : Type u_a} {B : Type u_b} {C : Type u_c}
  variables [s₁ : Setoid A] [s₂ : Setoid B]
  include s₁ s₂

  attribute [reducible, elab_as_eliminator]
  protected definition lift₂
     (f : A → B → C)(c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂)
     (q₁ : Quot s₁) (q₂ : Quot s₂) : C :=
  Quot.lift
    (λ (a₁ : A), Quot.lift (f a₁) (λ (a b : B), c a₁ a a₁ b (setoid_refl a₁)) q₂)
    (λ (a b : A) (H : a ≈ b),
       @Quot.ind B s₂
         (λ (a_1 : Quot s₂),
            (Quot.lift (f a) (λ (a_1 b : B), c a a_1 a b (setoid_refl a)) a_1)
            =
            (Quot.lift (f b) (λ (a b_1 : B), c b a b b_1 (setoid_refl b)) a_1))
         (λ (a' : B), c a a' b a' H (setoid_refl a'))
         q₂)
    q₁

  attribute [reducible, elab_as_eliminator]
  protected definition lift_on₂
    (q₁ : Quot s₁) (q₂ : Quot s₂) (f : A → B → C) (c : ∀ a₁ a₂ b₁ b₂, a₁ ≈ b₁ → a₂ ≈ b₂ → f a₁ a₂ = f b₁ b₂) : C :=
  Quot.lift₂ f c q₁ q₂

  attribute [elab_as_eliminator]
  protected theorem ind₂ {C : Quot s₁ → Quot s₂ → Prop} (H : ∀ a b, C ⟦a⟧ ⟦b⟧) (q₁ : Quot s₁) (q₂ : Quot s₂) : C q₁ q₂ :=
  Quot.ind (λ a₁, Quot.ind (λ a₂, H a₁ a₂) q₂) q₁

  attribute [elab_as_eliminator]
  protected theorem induction_on₂
     {C : Quot s₁ → Quot s₂ → Prop} (q₁ : Quot s₁) (q₂ : Quot s₂) (H : ∀ a b, C ⟦a⟧ ⟦b⟧) : C q₁ q₂ :=
  Quot.ind (λ a₁, Quot.ind (λ a₂, H a₁ a₂) q₂) q₁

  attribute [elab_as_eliminator]
  protected theorem induction_on₃
     [s₃ : Setoid C]
     {D : Quot s₁ → Quot s₂ → Quot s₃ → Prop} (q₁ : Quot s₁) (q₂ : Quot s₂) (q₃ : Quot s₃) (H : ∀ a b c, D ⟦a⟧ ⟦b⟧ ⟦c⟧)
     : D q₁ q₂ q₃ :=
  Quot.ind (λ a₁, Quot.ind (λ a₂, Quot.ind (λ a₃, H a₁ a₂ a₃) q₃) q₂) q₁
  end

  section exact
  variable {A : Type u}
  variable [s : Setoid A]
  include s

  private definition rel (q₁ q₂ : Quot s) : Prop :=
  Quot.lift_on₂ q₁ q₂
    (λ a₁ a₂, a₁ ≈ a₂)
    (λ a₁ a₂ b₁ b₂ a₁b₁ a₂b₂,
      propext (iff_intro
        (λ a₁a₂, setoid_trans (setoid_symm a₁b₁) (setoid_trans a₁a₂ a₂b₂))
        (λ b₁b₂, setoid_trans a₁b₁ (setoid_trans b₁b₂ (setoid_symm a₂b₂)))))

  local infix `~` := rel

  private lemma rel_refl : ∀ q : Quot s, q ~ q :=
  λ q, Quot.induction_on q (λ a, setoid_refl a)

  private lemma eq_imp_rel {q₁ q₂ : Quot s} : q₁ = q₂ → q₁ ~ q₂ :=
  assume h, eq.rec_on h (rel_refl q₁)

  theorem exact {a b : A} : ⟦a⟧ = ⟦b⟧ → a ≈ b :=
  assume h, eq_imp_rel h
  end exact

  section
  universe variables u_a u_b u_c
  variables {A : Type u_a} {B : Type u_b}
  variables [s₁ : Setoid A] [s₂ : Setoid B]
  include s₁ s₂

  attribute [reducible, elab_as_eliminator]
  protected definition rec_on_subsingleton₂
     {C : Quot s₁ → Quot s₂ → Type u_c} [H : ∀ a b, subsingleton (C ⟦a⟧ ⟦b⟧)]
     (q₁ : Quot s₁) (q₂ : Quot s₂) (f : Π a b, C ⟦a⟧ ⟦b⟧) : C q₁ q₂:=
  @Quot.rec_on_subsingleton _ s₁ (λ q, C q q₂) (λ a, Quot.ind (λ b, H a b) q₂) q₁
    (λ a, Quot.rec_on_subsingleton q₂ (λ b, f a b))

  end
end Quot

attribute Quot.mk

open Decidable
attribute [instance]
definition Quot.has_decidable_eq {A : Type u} {s : Setoid A} [decR : ∀ a b : A, Decidable (a ≈ b)] : DecidableEq (Quot s) :=
λ q₁ q₂ : Quot s,
  Quot.rec_on_subsingleton₂ q₁ q₂
    (λ a₁ a₂,
      match (decR a₁ a₂) with
      | (is_true h₁)  := is_true (Quot.sound h₁)
      | (is_false h₂) := is_false (λ h, absurd (Quot.exact h) h₂)
      end)
