/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.bool

namespace PosNum
  protected definition mul (a b : PosNum) : PosNum :=
  PosNum.rec_on a
    b
    (λn r, bit0 r + b)
    (λn r, bit0 r)

  definition lt (a b : PosNum) : Bool :=
  PosNum.rec_on a
    (λ b, PosNum.cases_on b
      ff
      (λm, tt)
      (λm, tt))
    (λn f b, PosNum.cases_on b
      ff
      (λm, f m)
      (λm, f m))
    (λn f b, PosNum.cases_on b
      ff
      (λm, f (succ m))
      (λm, f m))
    b

  definition le (a b : PosNum) : Bool :=
  PosNum.lt a (succ b)
end PosNum

attribute [instance]
definition mulPosNum : Mul PosNum :=
⟨PosNum.mul⟩

namespace Num
  open PosNum

  definition pred (a : Num) : Num :=
  Num.rec_on a zero (λp, cond (is_one p) zero (pos (pred p)))

  definition size (a : Num) : Num :=
  Num.rec_on a (pos PosNum.one) (λp, pos (size p))

  protected definition mul (a b : Num) : Num :=
  Num.rec_on a zero (λpa, Num.rec_on b zero (λpb, pos (PosNum.mul pa pb)))
end Num

attribute [instance]
definition mulNum : Mul Num :=
⟨Num.mul⟩

namespace Num
  protected definition le (a b : Num) : Bool :=
  Num.rec_on a tt (λpa, Num.rec_on b ff (λpb, PosNum.le pa pb))

  private definition psub (a b : PosNum) : Num :=
  PosNum.rec_on a
    (λb, zero)
    (λn f b,
      cond (PosNum.le (bit1 n) b)
        zero
        (PosNum.cases_on b
           (pos (bit0 n))
           (λm, 2 * f m)
           (λm, 2 * f m + 1)))
    (λn f b,
      cond (PosNum.le (bit0 n) b)
        zero
        (PosNum.cases_on b
           (pos (PosNum.pred (bit0 n)))
           (λm, pred (2 * f m))
           (λm, 2 * f m)))
    b

  protected definition sub (a b : Num) : Num :=
  Num.rec_on a zero (λpa, Num.rec_on b a (λpb, psub pa pb))
end Num

attribute [instance]
definition subNum : Sub Num :=
⟨Num.sub⟩
