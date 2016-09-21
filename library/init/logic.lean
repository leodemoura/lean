/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes

universe variables u v

attribute [reducible]
definition id {A : Type u} (a : A) : A :=
a

attribute [defeq]
definition id_def {A : Type u} (a : A) : id a = a :=
rfl


/- TODO(Leo): for new elaborator
- Support for partially applied recursors (use eta-expansion)
- checkpoints when processing calc.
-/

/- implication -/

definition implies (a b : Prop) := a → b

attribute [trans]
lemma implies_trans {p q r : Prop} (h₁ : implies p q) (h₂ : implies q r) : implies p r :=
assume hp, h₂ (h₁ hp)

definition trivial : true := ⟨⟩

definition not (a : Prop) := a → false
prefix `¬` := not

attribute [inline]
definition absurd {a : Prop} {b : Type v} (h₁ : a) (h₂ : ¬a) : b :=
false.rec b (h₂ h₁)

attribute [intro!]
lemma not_intro {a : Prop} (h : a → false) : ¬ a :=
h

theorem mt {a b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a :=
assume Ha : a, absurd (h₁ Ha) h₂

definition implies_resolve {a b : Prop} (h : a → b) (nb : ¬ b) : ¬ a := assume Ha, nb (h Ha)

/- not -/

theorem not_false : ¬false :=
assume h : false, h

definition non_contradictory (a : Prop) : Prop := ¬¬a

theorem non_contradictory_intro {a : Prop} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

/- false -/

theorem false.elim {c : Prop} (h : false) : c :=
false.rec c h

/- eq -/

-- proof irrelevance is built in
theorem proof_irrel {a : Prop} (h₁ h₂ : a) : h₁ = h₂ :=
rfl

-- Remark: we provide the universe levels explicitly to make sure `eq.drec` has the same type of `eq.rec` in the HoTT library
attribute [elab_as_eliminator]
protected theorem {u₁ u₂} eq.drec {A : Type u₂} {a : A} {C : Π (x : A), a = x → Type u₁} (h₁ : C a (eq.refl a)) {b : A} (h₂ : a = b) : C b h₂ :=
eq.rec (λh₂ : a = a, show C a h₂, from h₁) h₂ h₂

attribute [elab_as_eliminator]
protected theorem eq.drec_on {A : Type u} {a : A} {C : Π (x : A), a = x → Type v} {b : A} (h₂ : a = b) (h₁ : C a (eq.refl a)) : C b h₂ :=
eq.drec h₁ h₂

theorem eq_substr {A : Type u} {p : A → Prop} {a b : A} (h₁ : b = a) : p a → p b :=
eq.subst (eq_symm h₁)

theorem eq_mp {A B : Type u} : (A = B) → A → B :=
eq.rec_on

theorem eq_mpr {A B : Type u} : (A = B) → B → A :=
assume h₁ h₂, eq.rec_on (eq_symm h₁) h₂

theorem congr {A : Type u} {B : Type v} {f₁ f₂ : A → B} {a₁ a₂ : A} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
eq.subst h₁ (eq.subst h₂ rfl)

theorem congr_fun {A : Type u} {B : A → Type v} {f g : Π x, B x} (h : f = g) (a : A) : f a = g a :=
eq.subst h (eq.refl (f a))

theorem congr_arg {A : Type u} {B : Type v} {a₁ a₂ : A} (f : A → B) : a₁ = a₂ → f a₁ = f a₂ :=
congr rfl

theorem trans_rel_left {A : Type u} {a b c : A} (R : A → A → Prop) (h₁ : R a b) (h₂ : b = c) : R a c :=
h₂ ▸ h₁

theorem trans_rel_right {A : Type u} {a b c : A} (R : A → A → Prop) (h₁ : a = b) (h₂ : R b c) : R a c :=
eq_symm h₁ ▸ h₂

theorem of_eq_true {p : Prop} (h : p = true) : p :=
eq_symm h ▸ trivial

theorem not_of_eq_false {p : Prop} (h : p = false) : ¬p :=
assume Hp, h ▸ Hp

attribute [inline]
definition cast {A B : Type u} (h : A = B) (a : A) : B :=
eq.rec a h

theorem cast_proof_irrel {A B : Type u} (h₁ h₂ : A = B) (a : A) : cast h₁ a = cast h₂ a :=
rfl

theorem cast_eq {A : Type u} (h : A = A) (a : A) : cast h a = a :=
rfl

/- ne -/

attribute [reducible]
definition ne {A : Type u} (a b : A) := ¬(a = b)

notation a ≠ b := ne a b

attribute [defeq]
definition ne_def {A : Type u} (a b : A) : a ≠ b = ¬ (a = b) :=
rfl

theorem ne_irrefl {A : Type u} {a : A} (h : a ≠ a) : false :=
h rfl

theorem ne_symm {A : Type u} {a b : A} (h : a ≠ b) : b ≠ a :=
assume (h₁ : b = a), h (eq_symm h₁)

theorem false_of_ne {A : Type u} {a : A} : a ≠ a → false :=
ne_irrefl

theorem ne_false_of_self {p : Prop} : p → p ≠ false :=
assume (hp : p) (h : p = false), h ▸ hp

theorem ne_true_of_not {p : Prop} : ¬p → p ≠ true :=
assume (hnp : ¬p) (h : p = true), (h ▸ hnp) trivial

theorem true_ne_false {p : Prop} : ¬true = false :=
ne_false_of_self trivial

infixl ` == `:50 := heq

section
variables {A B C : Type u} {a a' : A} {b b' : B} {c : C}

theorem eq_of_heq (h : a == a') : a = a' :=
have ∀ (A' : Type u) (a' : A') (h₁ : @heq A a A' a') (h₂ : A = A'), (eq.rec_on h₂ a : A') = a', from
  λ (A' : Type u) (a' : A') (h₁ : @heq A a A' a'), heq.rec_on h₁ (λ h₂ : A = A, rfl),
show (eq.rec_on (eq.refl A) a : A) = a', from
  this A a' h (eq.refl A)

theorem heq.elim {A : Type u} {a : A} {P : A → Type v} {b : A} (h₁ : a == b)
: P a → P b := eq.rec_on (eq_of_heq h₁)

theorem heq.subst {p : ∀ T : Type u, T → Prop} : a == b → p A a → p B b :=
heq.rec_on

attribute heq.refl [refl]

attribute [symm]
theorem heq_symm (h : a == b) : b == a :=
heq.rec_on h (heq.refl a)

theorem heq_of_eq (h : a = a') : a == a' :=
eq.subst h (heq.refl a)

attribute [trans]
theorem heq_trans (h₁ : a == b) (h₂ : b == c) : a == c :=
heq.subst h₂ h₁

theorem heq_of_heq_of_eq (h₁ : a == b) (h₂ : b = b') : a == b' :=
heq_trans h₁ (heq_of_eq h₂)

theorem heq_of_eq_of_heq (h₁ : a = a') (h₂ : a' == b) : a == b :=
heq_trans (heq_of_eq h₁) h₂

definition type_eq_of_heq (h : a == b) : A = B :=
heq.rec_on h (eq.refl A)
end

theorem eq_rec_heq {A : Type u} {P : A → Type v} : ∀ {a a' : A} (h : a = a') (p : P a), (eq.rec_on h p : P a') == p
| a .a rfl p := heq.refl p

theorem heq_of_eq_rec_left {A : Type u} {P : A → Type v} : ∀ {a a' : A} {p₁ : P a} {p₂ : P a'} (e : a = a') (h₂ : (eq.rec_on e p₁ : P a') = p₂), p₁ == p₂
| a .a p₁ p₂ (eq.refl .a) h := eq.rec_on h (heq.refl p₁)

theorem heq_of_eq_rec_right {A : Type u} {P : A → Type v} : ∀ {a a' : A} {p₁ : P a} {p₂ : P a'} (e : a' = a) (h₂ : p₁ = eq.rec_on e p₂), p₁ == p₂
| a .a p₁ p₂ (eq.refl .a) h :=
  have p₁ = p₂, from h,
  this ▸ heq.refl p₁

theorem of_heq_true {a : Prop} (h : a == true) : a :=
of_eq_true (eq_of_heq h)

theorem eq_rec_compose : ∀ {A B C : Type u} (p₁ : B = C) (p₂ : A = B) (a : A), (eq.rec_on p₁ (eq.rec_on p₂ a : B) : C) = eq.rec_on (eq_trans p₂ p₁) a
| A .A .A (eq.refl .A) (eq.refl .A) a := rfl

theorem eq_rec_eq_eq_rec : ∀ {A₁ A₂ : Type u} {p : A₁ = A₂} {a₁ : A₁} {a₂ : A₂}, (eq.rec_on p a₁ : A₂) = a₂ → a₁ = eq.rec_on (eq_symm p) a₂
| A .A rfl a .a rfl := rfl

theorem eq_rec_of_heq_left : ∀ {A₁ A₂ : Type u} {a₁ : A₁} {a₂ : A₂} (h : a₁ == a₂), (eq.rec_on (type_eq_of_heq h) a₁ : A₂) = a₂
| A .A a .a (heq.refl .a) := rfl

theorem eq_rec_of_heq_right {A₁ A₂ : Type u} {a₁ : A₁} {a₂ : A₂} (h : a₁ == a₂) : a₁ = eq.rec_on (eq_symm (type_eq_of_heq h)) a₂ :=
eq_rec_eq_eq_rec (eq_rec_of_heq_left h)

theorem cast_heq : ∀ {A B : Type u} (h : A = B) (a : A), cast h a == a
| A .A (eq.refl .A) a := heq.refl a

/- and -/

notation a /\ b := and a b
notation a ∧ b  := and a b

variables {a b c d : Prop}

attribute and.rec [elim]
attribute and.intro [intro!]

theorem and_elim (h₁ : a ∧ b) (h₂ : a → b → c) : c :=
and.rec h₂ h₁

theorem and_swap : a ∧ b → b ∧ a :=
λ h, and.rec (λHa Hb, and.intro Hb Ha) h

/- or -/
notation a \/ b := or a b
notation a ∨ b := or a b

attribute [elim] or.rec

attribute [elab_as_eliminator]
theorem or_elim (h₁ : a ∨ b) (h₂ : a → c) (H₃ : b → c) : c :=
or.rec h₂ H₃ h₁

theorem non_contradictory_em (a : Prop) : ¬¬(a ∨ ¬a) :=
assume not_em : ¬(a ∨ ¬a),
  have neg_a : ¬a, from
    assume pos_a : a, absurd (or.inl pos_a) not_em,
  absurd (or.inr neg_a) not_em

theorem or_swap : a ∨ b → b ∨ a :=
or.rec or.inr or.inl

/- xor -/
definition xor (a b : Prop) := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

/- iff -/

definition iff (a b : Prop) := (a → b) ∧ (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

attribute [intro!]
theorem iff_intro : (a → b) → (b → a) → (a ↔ b) :=
and.intro

attribute [refl]
theorem iff_refl (a : Prop) : a ↔ a :=
iff_intro (assume H, H) (assume H, H)

theorem iff_rfl {a : Prop} : a ↔ a :=
iff_refl a

attribute [recursor 5, elim]
theorem iff_elim : ((a → b) → (b → a) → c) → (a ↔ b) → c :=
and.rec

theorem iff_elim_left : (a ↔ b) → a → b :=
and_left

definition iff_mp := @iff_elim_left

theorem iff_elim_right : (a ↔ b) → b → a :=
and_right

definition iff_mpr := @iff_elim_right

attribute [trans]
theorem iff_trans (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c :=
iff_intro
  (assume Ha, iff_mp h₂ (iff_mp h₁ Ha))
  (assume Hc, iff_mpr h₁ (iff_mpr h₂ Hc))

attribute [symm]
theorem iff_symm (h : a ↔ b) : b ↔ a :=
iff_intro (iff_elim_right h) (iff_elim_left h)

theorem iff_comm : (a ↔ b) ↔ (b ↔ a) :=
iff_intro iff_symm iff_symm

theorem iff_of_eq {a b : Prop} (h : a = b) : a ↔ b :=
eq.rec_on h iff_rfl

theorem not_iff_not_of_iff (h₁ : a ↔ b) : ¬a ↔ ¬b :=
iff_intro
 (assume (hna : ¬ a) (hb : b), hna (iff_elim_right h₁ hb))
 (assume (hnb : ¬ b) (ha : a), hnb (iff_elim_left h₁ ha))

theorem of_iff_true (h : a ↔ true) : a :=
iff_mp (iff_symm h) trivial

theorem not_of_iff_false : (a ↔ false) → ¬a :=
iff_mp

theorem iff_true_intro (h : a) : a ↔ true :=
iff_intro
  (λ h', trivial)
  (λ h', h)

theorem iff_false_intro (h : ¬a) : a ↔ false :=
iff_intro h (false.rec a)

theorem not_non_contradictory_iff_absurd (a : Prop) : ¬¬¬a ↔ ¬a :=
iff_intro
  (λ (Hl : ¬¬¬a) (Ha : a), Hl (non_contradictory_intro Ha))
  absurd

theorem imp_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a → b) ↔ (c → d) :=
iff_intro
  (λ hab hc, iff_mp h₂ (hab (iff_mpr h₁ hc)))
  (λ hcd ha, iff_mpr h₂ (hcd (iff_mp h₁ ha)))

theorem imp_congr_ctx (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : (a → b) ↔ (c → d) :=
iff_intro
  (λ hab hc,
    have ha : a, from iff_mpr h₁ hc,
    have hb : b, from hab ha,
    iff_mp (h₂ hc) hb)
  (λ hcd ha,
    have hc : c, from iff_mp h₁ ha,
    have hd : d, from hcd hc,
    iff_mpr (h₂ hc) hd)

theorem imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) :=
iff_intro
  (take hab ha, iff_elim_left (h ha) (hab ha))
  (take hab ha, iff_elim_right (h ha) (hab ha))

theorem not_not_intro (ha : a) : ¬¬a :=
assume hna : ¬a, hna ha

theorem not_of_not_not_not (h : ¬¬¬a) : ¬a :=
λ ha, absurd (not_not_intro ha) h

attribute [simp]
theorem not_true : (¬ true) ↔ false :=
iff_false_intro (not_not_intro trivial)

attribute [simp]
theorem not_false_iff : (¬ false) ↔ true :=
iff_true_intro not_false

attribute [congr]
theorem not_congr (h : a ↔ b) : ¬a ↔ ¬b :=
iff_intro (λ h₁ h₂, h₁ (iff_mpr h h₂)) (λ h₁ h₂, h₁ (iff_mp h h₂))

attribute [simp]
theorem ne_self_iff_false {A : Type u} (a : A) : (not (a = a)) ↔ false :=
iff_intro false_of_ne false.elim

attribute [simp]
theorem eq_self_iff_true {A : Type u} (a : A) : (a = a) ↔ true :=
iff_true_intro rfl

attribute [simp]
theorem heq_self_iff_true {A : Type u} (a : A) : (a == a) ↔ true :=
iff_true_intro (heq.refl a)

attribute [simp]
theorem iff_not_self (a : Prop) : (a ↔ ¬a) ↔ false :=
iff_false_intro (λ h,
   have h' : ¬a, from (λ ha, (iff_mp h ha) ha),
   h' (iff_mpr h h'))

attribute [simp]
theorem not_iff_self (a : Prop) : (¬a ↔ a) ↔ false :=
iff_false_intro (λ h,
   have h' : ¬a, from (λ ha, (iff_mpr h ha) ha),
   h' (iff_mp h h'))

attribute [simp]
theorem true_iff_false : (true ↔ false) ↔ false :=
iff_false_intro (λ h, iff_mp h trivial)

attribute [simp]
theorem false_iff_true : (false ↔ true) ↔ false :=
iff_false_intro (λ h, iff_mpr h trivial)

theorem false_of_true_iff_false : (true ↔ false) → false :=
assume h, iff_mp h trivial

/- and simp rules -/
theorem and_imp (h₂ : a → c) (h₃ : b → d) : a ∧ b → c ∧ d :=
λ h, and.rec (λ ha hb, ⟨h₂ ha, h₃ hb⟩) h

attribute [congr]
theorem and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∧ b) ↔ (c ∧ d) :=
iff_intro (and_imp (iff_mp h₁) (iff_mp h₂)) (and_imp (iff_mpr h₁) (iff_mpr h₂))

theorem and_congr_right (h : a → (b ↔ c)) : (a ∧ b) ↔ (a ∧ c) :=
iff_intro
  (take hab, ⟨and_left hab, iff_elim_left (h (and_left hab)) (and_right hab)⟩)
  (take hac, ⟨and_left hac, iff_elim_right (h (and_left hac)) (and_right hac)⟩)

attribute [simp]
theorem and_comm : a ∧ b ↔ b ∧ a :=
iff_intro and_swap and_swap

attribute [simp]
theorem and_assoc : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) :=
iff_intro
  (λ h, and.rec (λ h' hc, and.rec (λ ha hb, ⟨ha, hb, hc⟩) h') h)
  (λ h, and.rec (λ ha hbc, and.rec (λ hb hc, ⟨⟨ha, hb⟩, hc⟩) hbc) h)

attribute [simp]
theorem and_left_comm : a ∧ (b ∧ c) ↔ b ∧ (a ∧ c) :=
iff_trans (iff_symm and_assoc) (iff_trans (and_congr and_comm (iff_refl c)) and_assoc)

theorem and_iff_left {a b : Prop} (hb : b) : (a ∧ b) ↔ a :=
iff_intro and_left (λ ha, ⟨ha, hb⟩)

theorem and_iff_right {a b : Prop} (ha : a) : (a ∧ b) ↔ b :=
iff_intro and_right (and.intro ha)

attribute [simp]
theorem and_true (a : Prop) : a ∧ true ↔ a :=
and_iff_left trivial

attribute [simp]
theorem true_and (a : Prop) : true ∧ a ↔ a :=
and_iff_right trivial

attribute [simp]
theorem and_false (a : Prop) : a ∧ false ↔ false :=
iff_false_intro and_right

attribute [simp]
theorem false_and (a : Prop) : false ∧ a ↔ false :=
iff_false_intro and_left

attribute [simp]
theorem not_and_self (a : Prop) : (¬a ∧ a) ↔ false :=
iff_false_intro (λ h, and_elim h (λ h₁ h₂, absurd h₂ h₁))

attribute [simp]
theorem and_not_self (a : Prop) : (a ∧ ¬a) ↔ false :=
iff_false_intro (λ h, and_elim h (λ h₁ h₂, absurd h₁ h₂))

attribute [simp]
theorem and_self (a : Prop) : a ∧ a ↔ a :=
iff_intro and_left (assume h, ⟨h, h⟩)

/- or simp rules -/

theorem or_imp (h₂ : a → c) (h₃ : b → d) : a ∨ b → c ∨ d :=
or.rec (λ h, or.inl (h₂ h)) (λ h, or.inr (h₃ h))

theorem or_imp_left (h : a → b) : a ∨ c → b ∨ c :=
or_imp h id

theorem or_imp_right (h : a → b) : c ∨ a → c ∨ b :=
or_imp id h

attribute [congr]
theorem or_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∨ b) ↔ (c ∨ d) :=
iff_intro (or_imp (iff_mp h₁) (iff_mp h₂)) (or_imp (iff_mpr h₁) (iff_mpr h₂))

attribute [simp]
theorem or_comm : a ∨ b ↔ b ∨ a :=
iff_intro or_swap or_swap

attribute [simp]
theorem or_assoc : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) :=
iff_intro
  (or.rec (or_imp_right or.inl) (λ h, or.inr (or.inr h)))
  (or.rec (λ h, or.inl (or.inl h)) (or_imp_left or.inr))

attribute [simp]
theorem or_left_comm : a ∨ (b ∨ c) ↔ b ∨ (a ∨ c) :=
iff_trans (iff_symm or_assoc) (iff_trans (or_congr or_comm (iff_refl c)) or_assoc)

attribute [simp]
theorem or_true (a : Prop) : a ∨ true ↔ true :=
iff_true_intro (or.inr trivial)

attribute [simp]
theorem true_or (a : Prop) : true ∨ a ↔ true :=
iff_true_intro (or.inl trivial)

attribute [simp]
theorem or_false (a : Prop) : a ∨ false ↔ a :=
iff_intro (or.rec id false.elim) or.inl

attribute [simp]
theorem false_or (a : Prop) : false ∨ a ↔ a :=
iff_trans or_comm (or_false a)

attribute [simp]
theorem or_self (a : Prop) : a ∨ a ↔ a :=
iff_intro (or.rec id id) or.inl

/- or resolution rulse -/

definition or_resolve_left {a b : Prop} (h : a ∨ b) (na : ¬ a) : b :=
or_elim h (λ ha, absurd ha na) id

definition or_neg_resolve_left {a b : Prop} (h : ¬ a ∨ b) (ha : a) : b :=
or_elim h (λ na, absurd ha na) id

definition or_resolve_right {a b : Prop} (h : a ∨ b) (nb : ¬ b) : a :=
or_elim h id (λ hb, absurd hb nb)

definition or_neg_resolve_right {a b : Prop} (h : a ∨ ¬ b) (hb : b) : a :=
or_elim h id (λ nb, absurd hb nb)

/- iff simp rules -/

attribute [simp]
theorem iff_true (a : Prop) : (a ↔ true) ↔ a :=
iff_intro (assume h, iff_mpr h trivial) iff_true_intro

attribute [simp]
theorem true_iff (a : Prop) : (true ↔ a) ↔ a :=
iff_trans iff_comm (iff_true a)

attribute [simp]
theorem iff_false (a : Prop) : (a ↔ false) ↔ ¬ a :=
iff_intro and_left iff_false_intro

attribute [simp]
theorem false_iff (a : Prop) : (false ↔ a) ↔ ¬ a :=
iff_trans iff_comm (iff_false a)

attribute [simp]
theorem iff_self (a : Prop) : (a ↔ a) ↔ true :=
iff_true_intro iff_rfl

attribute [congr]
theorem iff_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
and_congr (imp_congr h₁ h₂) (imp_congr h₂ h₁)

/- exists -/

inductive Exists {A : Type u} (p : A → Prop) : Prop
| intro : ∀ (a : A), p a → Exists

attribute Exists.intro [intro]

definition exists_intro := @Exists.intro

notation `exists` binders `, ` r:(scoped P, Exists P) := r
notation `∃` binders `, ` r:(scoped P, Exists P) := r

attribute Exists.rec [elim]

theorem exists_elim {A : Type u} {p : A → Prop} {B : Prop}
  (h₁ : ∃x, p x) (h₂ : ∀ (a : A), p a → B) : B :=
Exists.rec h₂ h₁

/- exists unique -/

definition exists_unique {A : Type u} (p : A → Prop) :=
∃x, p x ∧ ∀y, p y → y = x

notation `∃!` binders `, ` r:(scoped P, exists_unique P) := r

attribute [intro]
theorem exists_unique.intro {A : Type u} {p : A → Prop} (w : A) (h₁ : p w) (h₂ : ∀y, p y → y = w) :
  ∃!x, p x :=
exists_intro w ⟨h₁, h₂⟩

attribute [recursor 4, elim]
theorem exists_unique_elim {A : Type u} {p : A → Prop} {b : Prop}
    (h₂ : ∃!x, p x) (h₁ : ∀x, p x → (∀y, p y → y = x) → b) : b :=
exists_elim h₂ (λ w hw, h₁ w (and_left hw) (and_right hw))

theorem exists_unique_of_exists_of_unique {A : Type u} {p : A → Prop}
    (hex : ∃ x, p x) (h_unique : ∀ y₁ y₂, p y₁ → p y₂ → y₁ = y₂) :  ∃! x, p x :=
exists_elim hex (λ x px, exists_unique.intro x px (take y, suppose p y, h_unique y x this px))

theorem exists_of_exists_unique {A : Type u} {p : A → Prop} (h : ∃! x, p x) : ∃ x, p x :=
exists_elim h (λ x Hx, ⟨x, and_left Hx⟩)

theorem unique_of_exists_unique {A : Type u} {p : A → Prop}
    (h : ∃! x, p x) {y₁ y₂ : A} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
exists_unique_elim h
  (take x, suppose p x,
    assume unique : ∀ y, p y → y = x,
    show y₁ = y₂, from eq_trans (unique _ py₁) (eq_symm (unique _ py₂)))

/- exists, forall, exists unique congruences -/
attribute [congr]
theorem forall_congr {A : Type u} {P Q : A → Prop} (h : ∀a, (P a ↔ Q a)) : (∀a, P a) ↔ ∀a, Q a :=
iff_intro (λ p a, iff_mp (h a) (p a)) (λ q a, iff_mpr (h a) (q a))

theorem exists_imp_exists {A : Type u} {P Q : A → Prop} (h : ∀a, (P a → Q a)) (p : ∃a, P a) : ∃a, Q a :=
exists_elim p (λ a Hp, ⟨a, h a Hp⟩)

attribute [congr]
theorem exists_congr {A : Type u} {P Q : A → Prop} (h : ∀a, (P a ↔ Q a)) : (Exists P) ↔ ∃a, Q a :=
iff_intro
  (exists_imp_exists (λa, iff_mp (h a)))
  (exists_imp_exists (λa, iff_mpr (h a)))

attribute [congr]
theorem exists_unique_congr {A : Type u} {p₁ p₂ : A → Prop} (h : ∀ x, p₁ x ↔ p₂ x) : (exists_unique p₁) ↔ (∃! x, p₂ x) := --
exists_congr (λ x, and_congr (h x) (forall_congr (λy, imp_congr (h y) iff_rfl)))

/- decidable -/

inductive [class] Decidable (p : Prop)
| is_false : ¬p → Decidable
| is_true :  p → Decidable

export Decidable (is_true is_false)

attribute [instance]
definition decidableTrue : Decidable true :=
is_true trivial

attribute [instance]
definition decidableFalse : Decidable false :=
is_false not_false

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
attribute [inline]
definition dite (c : Prop) [h : Decidable c] {A : Type u} : (c → A) → (¬ c → A) → A :=
λ t e, Decidable.rec_on h e t

/- if-then-else -/

attribute [inline]
definition ite (c : Prop) [h : Decidable c] {A : Type u} (t e : A) : A :=
Decidable.rec_on h (λ Hnc, e) (λ Hc, t)

namespace Decidable
  variables {p q : Prop}

  definition rec_on_true [h : Decidable p] {h₁ : p → Type u} {h₂ : ¬p → Type u} (h₃ : p) (h₄ : h₁ h₃)
      : Decidable.rec_on h h₂ h₁ :=
  Decidable.rec_on h (λ h, false.rec _ (h h₃)) (λh, h₄)

  definition rec_on_false [h : Decidable p] {h₁ : p → Type u} {h₂ : ¬p → Type u} (h₃ : ¬p) (h₄ : h₂ h₃)
      : Decidable.rec_on h h₂ h₁ :=
  Decidable.rec_on h (λh, h₄) (λh, false.rec _ (h₃ h))

  definition by_cases {q : Type u} [C : Decidable p] : (p → q) → (¬p → q) → q :=
  dite _

  theorem em (p : Prop) [Decidable p] : p ∨ ¬p := by_cases or.inl or.inr

  theorem by_contradiction [Decidable p] (h : ¬p → false) : p :=
  if h₁ : p then h₁ else false.rec _ (h h₁)

  definition to_bool (p : Prop) [h : Decidable p] : Bool :=
  Decidable.cases_on h (λ h₁, Bool.ff) (λ h₂, Bool.tt)
end Decidable

section
  variables {p q : Prop}
  definition  decidableOfDecidableOfIff (Hp : Decidable p) (h : p ↔ q) : Decidable q :=
  if Hp : p then is_true (iff_mp h Hp)
  else is_false (iff_mp (not_iff_not_of_iff h) Hp)

  definition  decidableOfDecidableOfEq (Hp : Decidable p) (h : p = q) : Decidable q :=
  decidableOfDecidableOfIff Hp (iff_of_eq h)

  protected definition or_by_cases [Decidable p] [Decidable q] {A : Type u}
                                   (h : p ∨ q) (h₁ : p → A) (h₂ : q → A) : A :=
  if hp : p then h₁ hp else
    if hq : q then h₂ hq else
      false.rec _ (or_elim h hp hq)
end

section
  variables {p q : Prop}

  attribute [instance]
  definition decidableAnd [Decidable p] [Decidable q] : Decidable (p ∧ q) :=
  if hp : p then
    if hq : q then is_true ⟨hp, hq⟩
    else is_false (assume h : p ∧ q, hq (and_right h))
  else is_false (assume h : p ∧ q, hp (and_left h))

  attribute [instance]
  definition decidableOr [Decidable p] [Decidable q] : Decidable (p ∨ q) :=
  if hp : p then is_true (or.inl hp) else
    if hq : q then is_true (or.inr hq) else
      is_false (or.rec hp hq)

  attribute [instance]
  definition decidableNot [Decidable p] : Decidable (¬p) :=
  if hp : p then is_false (absurd hp) else is_true hp

  attribute [instance]
  definition decidableImplies [Decidable p] [Decidable q] : Decidable (p → q) :=
  if hp : p then
    if hq : q then is_true (assume H, hq)
    else is_false (assume h : p → q, absurd (h hp) hq)
  else is_true (assume Hp, absurd Hp hp)

  attribute [instance]
  definition decidableIff [Decidable p] [Decidable q] : Decidable (p ↔ q) :=
  decidableAnd
end

attribute [reducible]
definition DecidablePred {A : Type u} (r : A → Prop) :=
Π (a : A), Decidable (r a)

attribute [reducible]
definition DecidableRel {A : Type u} (r : A → A → Prop) :=
Π (a b : A), Decidable (r a b)

attribute [reducible]
definition DecidableEq (A : Type u) :=
DecidableRel (@eq A)

attribute [instance]
definition decidableNe {A : Type u} [DecidableEq A] (a b : A) : Decidable (a ≠ b) :=
decidableImplies

theorem ff_ne_tt : ff = tt → false
.

definition is_dec_eq {A : Type u} (p : A → A → Bool) : Prop :=
∀ ⦃x y : A⦄, p x y = tt → x = y

definition is_dec_refl {A : Type u} (p : A → A → Bool) : Prop :=
∀ x, p x x = tt

open Decidable

attribute [instance]
protected definition decidableEqBool : DecidableEq Bool
| ff ff := is_true rfl
| ff tt := is_false ff_ne_tt
| tt ff := is_false (ne_symm ff_ne_tt)
| tt tt := is_true rfl

definition decidableEqOfBoolPred {A : Type u} {p : A → A → Bool} (h₁ : is_dec_eq p) (h₂ : is_dec_refl p) : DecidableEq A :=
take x y : A,
 if Hp : p x y = tt then is_true (h₁ Hp)
 else is_false (assume Hxy : x = y, absurd (h₂ y) (@eq.rec_on _ _ (λ z, ¬p z y = tt) _ Hxy Hp))

theorem decidableEqInlRefl {A : Type u} [h : DecidableEq A] (a : A) : h a a = is_true (eq.refl a) :=
match (h a a) with
| (is_true e)  := rfl
| (is_false n) := absurd rfl n
end

theorem decidableEqInrNeg {A : Type u} [h : DecidableEq A] {a b : A} : Π n : a ≠ b, h a b = is_false n :=
assume n,
match (h a b) with
| (is_true e)   := absurd e n
| (is_false n₁) := proof_irrel n n₁ ▸ eq.refl (is_false n)
end

/- inhabited -/

inductive [class] Inhabited (A : Type u)
| mk : A → Inhabited

attribute [inline]
protected definition Inhabited.value {A : Type u} : Inhabited A → A :=
λ h, Inhabited.rec (λ a, a) h

attribute [inline]
protected definition Inhabited.destruct {A : Type u} {B : Type v} (h₁ : Inhabited A) (h₂ : A → B) : B :=
Inhabited.rec h₂ h₁

attribute [inline]
definition default (A : Type u) [h : Inhabited A] : A :=
Inhabited.value h

attribute [inline, irreducible]
definition arbitrary (A : Type u) [h : Inhabited A] : A :=
Inhabited.value h

attribute [instance]
definition inhabitedProp : Inhabited Prop :=
⟨true⟩

attribute [instance]
definition inhabitedFun (A : Type u) {B : Type v} [h : Inhabited B] : Inhabited (A → B) :=
Inhabited.rec_on h (λ b, ⟨λ a, b⟩)

attribute [instance]
definition inhabitedPi (A : Type u) {B : A → Type v} [Π x, Inhabited (B x)] : Inhabited (Π x, B x) :=
⟨λ a, default (B a)⟩

attribute [inline, instance]
protected definition inhabitedBool : Inhabited Bool :=
⟨ff⟩

attribute [inline, instance]
protected definition inhabitedPosNum : Inhabited PosNum :=
⟨PosNum.one⟩

attribute [inline, instance]
protected definition inhabitedNum : Inhabited Num :=
⟨Num.zero⟩

inductive [class] nonempty (A : Type u) : Prop
| intro : A → nonempty

protected definition nonempty_elim {A : Type u} {B : Prop} (h₁ : nonempty A) (h₂ : A → B) : B :=
nonempty.rec h₂ h₁

attribute [instance]
theorem nonempty_of_inhabited {A : Type u} [Inhabited A] : nonempty A :=
⟨default A⟩

theorem nonempty_of_exists {A : Type u} {p : A → Prop} : (∃ x, p x) → nonempty A
| ⟨w, h⟩ := ⟨w⟩

/- subsingleton -/

inductive [class] subsingleton (A : Type u) : Prop
| intro : (∀ a b : A, a = b) → subsingleton

protected definition subsingleton_elim {A : Type u} [h : subsingleton A] : ∀(a b : A), a = b :=
subsingleton.rec (λp, p) h

protected definition subsingleton_helim {A B : Type u} [h : subsingleton A] (h : A = B) : ∀ (a : A) (b : B), a == b :=
eq.rec_on h (λ a b : A, heq_of_eq (subsingleton_elim a b))

attribute [instance]
definition subsingletonProp (p : Prop) : subsingleton p :=
⟨λ a b, proof_irrel a b⟩

attribute [instance]
definition subsingletonDecidable (p : Prop) : subsingleton (Decidable p) :=
subsingleton.intro (λ d₁,
  match d₁ with
  | (is_true t₁) := (λ d₂,
    match d₂ with
    | (is_true t₂) := eq.rec_on (proof_irrel t₁ t₂) rfl
    | (is_false f₂) := absurd t₁ f₂
    end)
  | (is_false f₁) := (λ d₂,
    match d₂ with
    | (is_true t₂) := absurd t₂ f₁
    | (is_false f₂) := eq.rec_on (proof_irrel f₁ f₂) rfl
    end)
  end)

protected theorem recSubsingleton {p : Prop} [h : Decidable p]
    {h₁ : p → Type u} {h₂ : ¬p → Type u}
    [h₃ : Π (h : p), subsingleton (h₁ h)] [h₄ : Π(h : ¬p), subsingleton (h₂ h)]
  : subsingleton (Decidable.rec_on h h₂ h₁) :=
match h with
| (is_true h)  := h₃ h
| (is_false h) := h₄ h
end

theorem if_pos {c : Prop} [h : Decidable c] (Hc : c) {A : Type u} {t e : A} : (ite c t e) = t :=
match h with
| (is_true  Hc)  := rfl
| (is_false Hnc) := absurd Hc Hnc
end

theorem if_neg {c : Prop} [h : Decidable c] (Hnc : ¬c) {A : Type u} {t e : A} : (ite c t e) = e :=
match h with
| (is_true Hc)   := absurd Hc Hnc
| (is_false Hnc) := rfl
end

attribute [simp]
theorem if_t_t (c : Prop) [h : Decidable c] {A : Type u} (t : A) : (ite c t t) = t :=
match h with
| (is_true Hc)   := rfl
| (is_false Hnc) := rfl
end

theorem implies_of_if_pos {c t e : Prop} [Decidable c] (h : ite c t e) : c → t :=
assume Hc, eq.rec_on (if_pos Hc : ite c t e = t) h

theorem implies_of_if_neg {c t e : Prop} [Decidable c] (h : ite c t e) : ¬c → e :=
assume Hnc, eq.rec_on (if_neg Hnc : ite c t e = e) h

theorem if_ctx_congr {A : Type u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                     {x y u v : A}
                     (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
match dec_b, dec_c with
| (is_false h₁), (is_false h₂) := h_e h₂
| (is_true h₁),  (is_true h₂)  := h_t h₂
| (is_false h₁), (is_true h₂)  := absurd h₂ (iff_mp (not_iff_not_of_iff h_c) h₁)
| (is_true h₁),  (is_false h₂) := absurd h₁ (iff_mpr (not_iff_not_of_iff h_c) h₂)
end

attribute [congr]
theorem if_congr {A : Type u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                 {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr A b c dec_b dec_c x y u v h_c (λ h, h_t) (λ h, h_e)

theorem if_ctx_simp_congr {A : Type u} {b c : Prop} [dec_b : Decidable b] {x y u v : A}
                        (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = (@ite c (decidableOfDecidableOfIff dec_b h_c) A u v) :=
@if_ctx_congr A b c dec_b (decidableOfDecidableOfIff dec_b h_c) x y u v h_c h_t h_e

attribute [congr]
theorem if_simp_congr {A : Type u} {b c : Prop} [dec_b : Decidable b] {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidableOfDecidableOfIff dec_b h_c) A u v) :=
@if_ctx_simp_congr A b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)

attribute [simp]
definition if_true {A : Type u} (t e : A) : (if true then t else e) = t :=
if_pos trivial

attribute [simp]
definition if_false {A : Type u} (t e : A) : (if false then t else e) = e :=
if_neg not_false

theorem if_ctx_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                      (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ ite c u v :=
match dec_b, dec_c with
| (is_false h₁), (is_false h₂) := h_e h₂
| (is_true h₁),  (is_true h₂)  := h_t h₂
| (is_false h₁), (is_true h₂)  := absurd h₂ (iff_mp (not_iff_not_of_iff h_c) h₁)
| (is_true h₁),  (is_false h₂) := absurd h₁ (iff_mpr (not_iff_not_of_iff h_c) h₂)
end

attribute [congr]
theorem if_congr_prop {b c x y u v : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                      (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v :=
if_ctx_congr_prop h_c (λ h, h_t) (λ h, h_e)

theorem if_ctx_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite c (decidableOfDecidableOfIff dec_b h_c) Prop u v) :=
@if_ctx_congr_prop b c x y u v dec_b (decidableOfDecidableOfIff dec_b h_c) h_c h_t h_e

attribute [congr]
theorem if_simp_congr_prop {b c x y u v : Prop} [dec_b : Decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite c (decidableOfDecidableOfIff dec_b h_c) Prop u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ h, h_t) (λ h, h_e)

theorem dif_pos {c : Prop} [h : Decidable c] (Hc : c) {A : Type u} {t : c → A} {e : ¬ c → A} : dite c t e = t Hc :=
match h with
| (is_true Hc)   := rfl
| (is_false Hnc) := absurd Hc Hnc
end

theorem dif_neg {c : Prop} [h : Decidable c] (Hnc : ¬c) {A : Type u} {t : c → A} {e : ¬ c → A} : dite c t e = e Hnc :=
match h with
| (is_true Hc)   := absurd Hc Hnc
| (is_false Hnc) := rfl
end

theorem dif_ctx_congr {A : Type u} {b c : Prop} [dec_b : Decidable b] [dec_c : Decidable c]
                      {x : b → A} {u : c → A} {y : ¬b → A} {v : ¬c → A}
                      (h_c : b ↔ c)
                      (h_t : ∀ (h : c),    x (iff_mpr h_c h)                      = u h)
                      (h_e : ∀ (h : ¬c),   y (iff_mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b A x y) = (@dite c dec_c A u v) :=
match dec_b, dec_c with
| (is_false h₁), (is_false h₂) := h_e h₂
| (is_true h₁),  (is_true h₂)  := h_t h₂
| (is_false h₁), (is_true h₂)  := absurd h₂ (iff_mp (not_iff_not_of_iff h_c) h₁)
| (is_true h₁),  (is_false h₂) := absurd h₁ (iff_mpr (not_iff_not_of_iff h_c) h₂)
end

theorem dif_ctx_simp_congr {A : Type u} {b c : Prop} [dec_b : Decidable b]
                         {x : b → A} {u : c → A} {y : ¬b → A} {v : ¬c → A}
                         (h_c : b ↔ c)
                         (h_t : ∀ (h : c),    x (iff_mpr h_c h)                      = u h)
                         (h_e : ∀ (h : ¬c),   y (iff_mpr (not_iff_not_of_iff h_c) h) = v h) :
        (@dite b dec_b A x y) = (@dite c (decidableOfDecidableOfIff dec_b h_c) A u v) :=
@dif_ctx_congr A b c dec_b (decidableOfDecidableOfIff dec_b h_c) x u y v h_c h_t h_e

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
theorem dite_ite_eq (c : Prop) [h : Decidable c] {A : Type u} (t : A) (e : A) : dite c (λh, t) (λh, e) = ite c t e :=
match h with
| (is_true Hc)   := rfl
| (is_false Hnc) := rfl
end

-- The following symbols should not be considered in the pattern inference procedure used by
-- heuristic instantiation.
attribute and or not iff ite dite eq ne heq [no_pattern]

definition as_true (c : Prop) [Decidable c] : Prop :=
if c then true else false

definition as_false (c : Prop) [Decidable c] : Prop :=
if c then false else true

definition of_as_true {c : Prop} [h₁ : Decidable c] (h₂ : as_true c) : c :=
match h₁, h₂ with
| (is_true h_c),  h₂ := h_c
| (is_false h_c), h₂ := false.elim h₂
end

-- namespace used to collect congruence rules for "contextual simplification"
namespace contextual
  attribute if_ctx_simp_congr      [congr]
  attribute if_ctx_simp_congr_prop [congr]
  attribute dif_ctx_simp_congr     [congr]
end contextual
