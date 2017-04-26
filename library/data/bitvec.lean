/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.vector

@[reducible] def bitvec (n : ℕ) := vector bool n

namespace bitvec
open nat
open vector

local infix `++ₜ`:65 := vector.append

-- Create a zero bitvector
@[reducible] protected def zero (n : ℕ) : bitvec n := repeat ff n

-- Create a bitvector with the constant one.
@[reducible] protected def one : Π (n : ℕ), bitvec n
| 0        := []
| (succ n) := repeat ff n ++ₜ [tt]

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

-- bitvec specific version of vector.append
def append {m n} : bitvec m → bitvec n → bitvec (m + n) := vector.append

section shift
  variable {n : ℕ}

  def shl (x : bitvec n) (i : ℕ) : bitvec n :=
  bitvec.cong (by simp) $
    dropn i x ++ₜ repeat ff (min n i)

  local attribute [ematch] nat.add_sub_assoc sub_le le_of_not_ge sub_eq_zero_of_le
  def fill_shr (x : bitvec n) (i : ℕ) (fill : bool) : bitvec n :=
  bitvec.cong (begin [smt] by_cases (i ≤ n), eblast, trace_state end) $
    repeat fill (min n i) ++ₜ taken (n-i) x

#exit

  -- unsigned shift right
  def ushr (x : bitvec n) (i : ℕ) : bitvec n :=
  fill_shr x i ff

  -- signed shift right
  def sshr : Π {m : ℕ}, bitvec m → ℕ → bitvec m
  | 0        _ _ := []
  | (succ m) x i := head x :: fill_shr (tail x) i (head x)

end shift

section bitwise
  variable {n : ℕ}

  def not : bitvec n → bitvec n := map bnot
  def and : bitvec n → bitvec n → bitvec n := map₂ band
  def or  : bitvec n → bitvec n → bitvec n := map₂ bor
  def xor : bitvec n → bitvec n → bitvec n := map₂ bxor

end bitwise

section arith
  variable {n : ℕ}

  protected def xor3 (x y c : bool) := bxor (bxor x y) c
  protected def carry (x y c : bool) :=
  x && y || x && c || y && c

  protected def neg (x : bitvec n) : bitvec n :=
  let f := λ y c, (y || c, bxor y c) in
  prod.snd (map_accumr f x ff)

  -- Add with carry (no overflow)
  def adc (x y : bitvec n) (c : bool) : bitvec (n+1) :=
  let f := λ x y c, (bitvec.carry x y c, bitvec.xor3 x y c) in
  let ⟨c, z⟩ := vector.map_accumr₂ f x y c in
  c :: z

  protected def add (x y : bitvec n) : bitvec n := tail (adc x y ff)

  protected def borrow (x y b : bool) :=
  bnot x && y || bnot x && b || y && b

  -- Subtract with borrow
  def sbb (x y : bitvec n) (b : bool) : bool × bitvec n :=
  let f := λ x y c, (bitvec.borrow x y c, bitvec.xor3 x y c) in
  vector.map_accumr₂ f x y b

  protected def sub (x y : bitvec n) : bitvec n := prod.snd (sbb x y ff)

  instance : has_zero (bitvec n) := ⟨bitvec.zero n⟩
  instance : has_one (bitvec n)  := ⟨bitvec.one n⟩
  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n :=
  let f := λ r b, cond b (r + r + y) (r + r) in
  (to_list x).foldl f 0

  instance : has_mul (bitvec n)  := ⟨bitvec.mul⟩
end arith

section comparison
  variable {n : ℕ}

  def uborrow (x y : bitvec n) : bool := prod.fst (sbb x y ff)

  def ult (x y : bitvec n) : Prop := uborrow x y
  def ugt (x y : bitvec n) : Prop := ult y x

  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
  | 0        _ _ := ff
  | (succ n) x y :=
    match (head x, head y) with
    | (tt, ff) := tt
    | (ff, tt) := ff
    | _        := uborrow (tail x) (tail y)
    end

  def slt (x y : bitvec n) : Prop := sborrow x y
  def sgt (x y : bitvec n) : Prop := slt y x
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  def sge (x y : bitvec n) : Prop := sle y x

end comparison

section conversion
  variable {α : Type}

  protected def of_nat : Π (n : ℕ), nat → bitvec n
  | 0        x := nil
  | (succ n) x := of_nat n (x / 2) ++ₜ [to_bool (x % 2 = 1)]

  protected def of_int : Π (n : ℕ), int → bitvec (succ n)
  | n (int.of_nat m)          := ff :: bitvec.of_nat n m
  | n (int.neg_succ_of_nat m) := tt :: not (bitvec.of_nat n m)

  def add_lsb (r : ℕ) (b : bool) := r + r + cond b 1 0

  def bits_to_nat (v : list bool) : nat :=
  v.foldl add_lsb 0

  protected def to_nat {n : nat} (v : bitvec n) : nat :=
  bits_to_nat (to_list v)

  lemma bits_to_nat_to_list {n : ℕ} (x : bitvec n)
  : bitvec.to_nat x = bits_to_nat (vector.to_list x)  := rfl

  theorem to_nat_append {m : ℕ} (xs : bitvec m) (b : bool)
  : bitvec.to_nat (xs ++ₜ[b]) = bitvec.to_nat xs * 2 + bitvec.to_nat [b] :=
  begin
    cases xs with xs P,
    simp [bits_to_nat_to_list], clear P,
    unfold bits_to_nat list.foldl,
      -- the next 4 lines generalize the accumulator of foldl
    pose x := 0,
    change _ = add_lsb x b + _,
    generalize 0 y,
    revert x, simp,
    induction xs with x xs ; intro y,
    { simp, unfold list.foldl add_lsb, simp [nat.mul_succ] },
    { simp, unfold list.foldl, apply ih_1 }
  end

  theorem bits_to_nat_to_bool (n : ℕ)
  : bitvec.to_nat [to_bool (n % 2 = 1)] = n % 2 :=
  begin
    simp [bits_to_nat_to_list],
    unfold bits_to_nat add_lsb list.foldl cond,
    simp [cond_to_bool_mod_two],
  end

  lemma of_nat_succ {k n : ℕ}
  :  bitvec.of_nat (succ k) n = bitvec.of_nat k (n / 2) ++ₜ[to_bool (n % 2 = 1)] :=
  rfl

  theorem to_nat_of_nat {k n : ℕ}
  : bitvec.to_nat (bitvec.of_nat k n) = n % 2^k :=
  begin
    revert n,
    induction k with k ; intro n,
    { unfold pow, simp [nat.mod_one], refl },
    { assert h : 0 < 2, { apply le_succ },
      rw [ of_nat_succ
         , to_nat_append
         , ih_1
         , bits_to_nat_to_bool
         , mod_pow_succ h],
      ac_refl, }
  end

  protected def to_int : Π {n : nat}, bitvec n → int
  | 0        _ := 0
  | (succ n) v :=
    cond (head v)
      (int.neg_succ_of_nat $ bitvec.to_nat $ not $ tail v)
      (int.of_nat $ bitvec.to_nat $ tail v)

end conversion

private def to_string {n : nat} : bitvec n → string
| ⟨bs, p⟩ :=
  "0b" ++ (bs.reverse.map (λ b, if b then #"1" else #"0"))

instance (n : nat) : has_to_string (bitvec n) :=
⟨to_string⟩
end bitvec

instance {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _
instance {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _
