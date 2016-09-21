/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.relation init.num

notation `ℕ` := Nat

attribute [instance]
protected definition inhabitedNat : Inhabited Nat :=
⟨Nat.zero⟩

attribute [instance, priority Nat.prio]
definition decidableEqNat : ∀ x y : Nat, Decidable (x = y)
| Nat.zero     Nat.zero     := is_true rfl
| (Nat.succ x) Nat.zero     := is_false (λ h, Nat.no_confusion h)
| Nat.zero     (Nat.succ y) := is_false (λ h, Nat.no_confusion h)
| (Nat.succ x) (Nat.succ y) :=
    match decidableEqNat x y with
    | is_true xeqy := is_true (xeqy ▸ eq.refl (Nat.succ x))
    | is_false xney := is_false (λ h, Nat.no_confusion h (λ xeqy, absurd xeqy xney))
    end

namespace Nat
  protected theorem zero_add : ∀ n : ℕ, 0 + n = n
  | 0     := rfl
  | (n+1) := congr_arg succ (zero_add n)

  theorem succ_add : ∀ n m : ℕ, (succ n) + m = succ (n + m)
  | n 0     := rfl
  | n (m+1) := congr_arg succ (succ_add n m)

  protected theorem add_comm : ∀ n m : ℕ, n + m = m + n
  | n 0     := eq_symm (Nat.zero_add n)
  | n (m+1) :=
    suffices succ (n + m) = succ (m + n), from
      eq_symm (succ_add m n) ▸ this,
    congr_arg succ (add_comm n m)

  protected theorem bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
  show succ (succ n + n) = succ (succ (n + n)), from
  succ_add n n ▸ rfl

  protected theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
  rfl

  protected theorem bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
  eq_trans (Nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (Nat.bit0_succ_eq n))

  theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
  assume h, Nat.no_confusion h

  theorem succ_ne_self : ∀ n : ℕ, succ n ≠ n
  | 0     h := absurd h (Nat.succ_ne_zero 0)
  | (n+1) h := succ_ne_self n (Nat.no_confusion h (λ h, h))

  protected theorem one_ne_zero : 1 ≠ (0 : ℕ) :=
  assume h, Nat.no_confusion h

  protected theorem bit0_ne_zero : ∀ n : ℕ, n ≠ 0 → bit0 n ≠ 0
  | 0     h := absurd rfl h
  | (n+1) h := Nat.succ_ne_zero _

  protected theorem bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
  show succ (n + n) ≠ 0, from
  succ_ne_zero (n + n)

  protected theorem bit1_ne_one : ∀ n : ℕ, n ≠ 0 → bit1 n ≠ 1
  | 0     h h1 := absurd rfl h
  | (n+1) h h1 := Nat.no_confusion h1 (λ h2, absurd h2 (Nat.succ_ne_zero _))

  protected theorem bit0_ne_one : ∀ n : ℕ, bit0 n ≠ 1
  | 0     h := absurd h (ne_symm Nat.one_ne_zero)
  | (n+1) h :=
    have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
    Nat.no_confusion h1
      (λ h2, absurd h2 (succ_ne_zero (n + n)))

  protected theorem add_self_ne_one : ∀ (n : ℕ), n + n ≠ 1
  | 0     h := Nat.no_confusion h
  | (n+1) h :=
    have h1 : succ (succ (n + n)) = 1, from succ_add n n ▸ h,
    Nat.no_confusion h1 (λ h2, absurd h2 (Nat.succ_ne_zero (n + n)))

  protected theorem bit1_ne_bit0 : ∀ (n m : ℕ), bit1 n ≠ bit0 m
  | 0     m     h := absurd h (ne_symm (Nat.add_self_ne_one m))
  | (n+1) 0     h :=
    have h1 : succ (bit0 (succ n)) = 0, from h,
    absurd h1 (Nat.succ_ne_zero _)
  | (n+1) (m+1) h :=
    have h1 : succ (succ (bit1 n)) = succ (succ (bit0 m)), from
      Nat.bit0_succ_eq m ▸ Nat.bit1_succ_eq n ▸ h,
    have h2 : bit1 n = bit0 m, from
      Nat.no_confusion h1 (λ h2', Nat.no_confusion h2' (λ h2'', h2'')),
    absurd h2 (bit1_ne_bit0 n m)

  inductive le (a : ℕ) : ℕ → Prop
  | nat_refl : le a    -- use nat_refl to avoid overloading le.refl
  | step : Π {b}, le b → le (succ b)

  attribute [instance, priority Nat.prio]
  definition leNat : Le ℕ :=
  ⟨Nat.le⟩

  attribute [refl]
  protected definition le_refl : ∀ a : ℕ, a ≤ a :=
  le.nat_refl

  attribute [reducible]
  protected definition lt (n m : ℕ) := succ n ≤ m

  attribute [instance, priority Nat.prio]
  definition ltNat : Lt ℕ :=
  ⟨Nat.lt⟩

  definition pred : ℕ → ℕ
  | 0     := 0
  | (a+1) := a

  protected definition sub : ℕ → ℕ → ℕ
  | a 0     := a
  | a (b+1) := pred (sub a b)

  protected definition mul (a b : ℕ) : ℕ :=
  Nat.rec_on b zero (λ b₁ r, r + a)

  attribute [instance, priority Nat.prio]
  definition subNat : Sub ℕ :=
  ⟨Nat.sub⟩

  attribute [instance, priority Nat.prio]
  definition mulNat : Mul ℕ :=
  ⟨Nat.mul⟩

  /- properties of inequality -/

  protected theorem le_of_eq {n m : ℕ} (p : n = m) : n ≤ m :=
  p ▸ le.nat_refl n

  theorem le_succ (n : ℕ) : n ≤ succ n :=
  le.step (Nat.le_refl n)

  theorem pred_le : ∀ (n : ℕ), pred n ≤ n
  | 0        := le.nat_refl 0
  | (succ a) := le.step (le.nat_refl a)

  attribute [simp]
  theorem le_succ_iff_true (n : ℕ) : n ≤ succ n ↔ true :=
  iff_true_intro (le_succ n)

  attribute [simp]
  theorem pred_le_iff_true (n : ℕ) : pred n ≤ n ↔ true :=
  iff_true_intro (pred_le n)

  protected theorem le_trans {n m k : ℕ} (H1 : n ≤ m) : m ≤ k → n ≤ k :=
  le.rec H1 (λp H2, le.step)

  theorem le_succ_of_le {n m : ℕ} (H : n ≤ m) : n ≤ succ m :=
  Nat.le_trans H (le_succ m)

  theorem le_of_succ_le {n m : ℕ} (H : succ n ≤ m) : n ≤ m :=
  Nat.le_trans (le_succ n) H

  protected theorem le_of_lt {n m : ℕ} (H : n < m) : n ≤ m :=
  le_of_succ_le H

  theorem succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
  λ H, le.rec (Nat.le_refl (succ n)) (λ a b, le.step) H

  theorem pred_le_pred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
  λ H, le.rec (Nat.le_refl (pred n)) (λ n, Nat.rec (λ a b, b) (λ a b c, le.step) n) H

  theorem le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
  pred_le_pred

  theorem le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
  Nat.cases_on n le.step (λa, succ_le_succ)

  theorem not_succ_le_zero : ∀ (n : ℕ), succ n ≤ 0 → false
  .

  theorem succ_le_zero_iff_false (n : ℕ) : succ n ≤ 0 ↔ false :=
  iff_false_intro (not_succ_le_zero n)

  theorem not_succ_le_self : ∀ n : ℕ, ¬succ n ≤ n :=
  λ n, Nat.rec (not_succ_le_zero 0) (λa b c, b (le_of_succ_le_succ c)) n

  attribute [simp]
  theorem succ_le_self_iff_false (n : ℕ) : succ n ≤ n ↔ false :=
  iff_false_intro (not_succ_le_self n)

  theorem zero_le : ∀ (n : ℕ), 0 ≤ n
  | 0     := Nat.le_refl 0
  | (n+1) := le.step (zero_le n)

  attribute [simp]
  theorem zero_le_iff_true (n : ℕ) : 0 ≤ n ↔ true :=
  iff_true_intro (zero_le n)

  protected theorem one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  show 1 ≤ succ (bit0 n), from
  succ_le_succ (zero_le (bit0 n))

  protected theorem one_le_bit0 : ∀ (n : ℕ), n ≠ 0 → 1 ≤ bit0 n
  | 0     h := absurd rfl h
  | (n+1) h :=
    suffices 1 ≤ succ (succ (bit0 n)), from
      eq_symm (Nat.bit0_succ_eq n) ▸ this,
    succ_le_succ (zero_le (succ (bit0 n)))

  definition lt.step {n m : ℕ} : n < m → n < succ m := le.step

  theorem zero_lt_succ (n : ℕ) : 0 < succ n :=
  succ_le_succ (zero_le n)

  attribute [simp]
  theorem zero_lt_succ_iff_true (n : ℕ) : 0 < succ n ↔ true :=
  iff_true_intro (zero_lt_succ n)

  protected theorem lt_trans {n m k : ℕ} (H1 : n < m) : m < k → n < k :=
  Nat.le_trans (le.step H1)

  protected theorem lt_of_le_of_lt {n m k : ℕ} (H1 : n ≤ m) : m < k → n < k :=
  Nat.le_trans (succ_le_succ H1)

  protected theorem lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k := Nat.le_trans

  protected theorem lt_irrefl (n : ℕ) : ¬n < n :=
  not_succ_le_self n

  theorem lt_self_iff_false (n : ℕ) : n < n ↔ false :=
  iff_false_intro (λ H, absurd H (Nat.lt_irrefl n))

  theorem self_lt_succ (n : ℕ) : n < succ n := Nat.le_refl (succ n)

  attribute [simp]
  theorem self_lt_succ_iff_true (n : ℕ) : n < succ n ↔ true :=
  iff_true_intro (self_lt_succ n)

  definition lt.base (n : ℕ) : n < succ n := Nat.le_refl (succ n)

  theorem le_lt_antisymm {n m : ℕ} (H1 : n ≤ m) (H2 : m < n) : false :=
  Nat.lt_irrefl n (Nat.lt_of_le_of_lt H1 H2)

  protected theorem le_antisymm {n m : ℕ} (H1 : n ≤ m) : m ≤ n → n = m :=
  le.cases_on H1 (λa, rfl) (λa b c, absurd (Nat.lt_of_le_of_lt b c) (Nat.lt_irrefl n))

  theorem lt_le_antisymm {n m : ℕ} (H1 : n < m) (H2 : m ≤ n) : false :=
  le_lt_antisymm H2 H1

  protected theorem Nat.lt_asymm {n m : ℕ} (H1 : n < m) : ¬ m < n :=
  le_lt_antisymm (Nat.le_of_lt H1)

  theorem not_lt_zero (a : ℕ) : ¬ a < 0 := not_succ_le_zero a

  attribute [simp]
  theorem lt_zero_iff_false (a : ℕ) : a < 0 ↔ false :=
  iff_false_intro (not_lt_zero a)

  protected theorem eq_or_lt_of_le {a b : ℕ} (H : a ≤ b) : a = b ∨ a < b :=
  le.cases_on H (or.inl rfl) (λn h, or.inr (succ_le_succ h))

  protected theorem le_of_eq_or_lt {a b : ℕ} (H : a = b ∨ a < b) : a ≤ b :=
  or_elim H Nat.le_of_eq Nat.le_of_lt

  theorem succ_lt_succ {a b : ℕ} : a < b → succ a < succ b :=
  succ_le_succ

  theorem lt_of_succ_lt {a b : ℕ} : succ a < b → a < b :=
  le_of_succ_le

  theorem lt_of_succ_lt_succ {a b : ℕ} : succ a < succ b → a < b :=
  le_of_succ_le_succ

  attribute [instance, priority Nat.prio]
  protected definition decidableLe : ∀ a b : Nat, Decidable (a ≤ b)
  | 0     b     := is_true (zero_le b)
  | (a+1) 0     := is_false (not_succ_le_zero a)
  | (a+1) (b+1) :=
    match decidableLe a b with
    | is_true H  := is_true (succ_le_succ H)
    | is_false H := is_false (λa, H (le_of_succ_le_succ a))
    end

  attribute [instance, priority Nat.prio]
  protected definition decidableLt : ∀ a b : Nat, Decidable (a < b) :=
  λ a b, Nat.decidableLe (succ a) b

  protected theorem lt_or_ge : ∀ (a b : ℕ), a < b ∨ a ≥ b
  | a 0     := or.inr (zero_le a)
  | a (b+1) :=
    match lt_or_ge a b with
    | or.inl h := or.inl (le_succ_of_le h)
    | or.inr h :=
      match Nat.eq_or_lt_of_le h with
      | or.inl h1 := or.inl (h1 ▸ self_lt_succ b)
      | or.inr h1 := or.inr h1
      end
    end

  protected definition {u} lt_ge_by_cases {a b : ℕ} {P : Type u} (H1 : a < b → P) (H2 : a ≥ b → P) : P :=
  Decidable.by_cases H1 (λh, H2 (or_elim (Nat.lt_or_ge a b) (λa, absurd a h) (λa, a)))

  protected definition {u} lt_by_cases {a b : ℕ} {P : Type u} (H1 : a < b → P) (H2 : a = b → P)
    (H3 : b < a → P) : P :=
  Nat.lt_ge_by_cases H1 (λh₁,
    Nat.lt_ge_by_cases H3 (λh₂, H2 (Nat.le_antisymm h₂ h₁)))

  protected theorem lt_trichotomy (a b : ℕ) : a < b ∨ a = b ∨ b < a :=
  Nat.lt_by_cases (λH, or.inl H) (λH, or.inr (or.inl H)) (λH, or.inr (or.inr H))

  protected theorem eq_or_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ∨ b < a :=
  or_elim (Nat.lt_trichotomy a b)
    (λ hlt, absurd hlt hnlt)
    (λ h, h)

  theorem lt_succ_of_le {a b : ℕ} : a ≤ b → a < succ b :=
  succ_le_succ

  theorem lt_of_succ_le {a b : ℕ} (h : succ a ≤ b) : a < b := h

  theorem succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b := h

  attribute [simp]
  theorem succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
  Nat.rec_on b
    (show succ a - succ zero = a - zero, from (eq.refl (succ a - succ zero)))
    (λ b, congr_arg pred)

  theorem sub_eq_succ_sub_succ (a b : ℕ) : a - b = succ a - succ b :=
  eq_symm (succ_sub_succ_eq_sub a b)

  attribute [simp]
  theorem zero_sub_eq_zero : ∀ a : ℕ, 0 - a = 0
  | 0     := rfl
  | (a+1) := congr_arg pred (zero_sub_eq_zero a)

  theorem zero_eq_zero_sub (a : ℕ) : 0 = 0 - a :=
  eq_symm (zero_sub_eq_zero a)

  theorem sub_le (a b : ℕ) : a - b ≤ a :=
  Nat.rec_on b (Nat.le_refl (a - 0)) (λ b₁, Nat.le_trans (pred_le (a - b₁)))

  attribute [simp]
  theorem sub_le_iff_true (a b : ℕ) : a - b ≤ a ↔ true :=
  iff_true_intro (sub_le a b)

  theorem sub_lt : ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
  | 0     b     h1 h2 := absurd h1 (Nat.lt_irrefl 0)
  | (a+1) 0     h1 h2 := absurd h2 (Nat.lt_irrefl 0)
  | (a+1) (b+1) h1 h2 :=
    eq_symm (succ_sub_succ_eq_sub a b) ▸
      show a - b < succ a, from
      lt_succ_of_le (sub_le a b)

  theorem sub_lt_succ (a b : ℕ) : a - b < succ a :=
  lt_succ_of_le (sub_le a b)

  attribute [simp]
  theorem sub_lt_succ_iff_true (a b : ℕ) : a - b < succ a ↔ true :=
  iff_true_intro (sub_lt_succ a b)

  theorem le_add_right : ∀ (n k : ℕ), n ≤ n + k
  | n 0     := Nat.le_refl n
  | n (k+1) := le_succ_of_le (le_add_right n k)

  theorem le_add_left (n m : ℕ): n ≤ m + n :=
  Nat.add_comm n m ▸ le_add_right n m

  definition {u} repeat {A : Type u} (f : ℕ → A → A) : ℕ → A → A
  | 0         a := a
  | (succ n)  a := f n (repeat n a)

end Nat
