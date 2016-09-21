-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
prelude
import init.wf
universe variables u
namespace well_founded
  -- This is an auxiliary definition that useful for generating a new "proof" for (well_founded R)
  -- that allows us to use well_founded.fix and execute the definitions up to k nested recursive
  -- calls without "computing" with the proofs in Hwf.
  definition intro_k {A : Type u} {r : A → A → Prop} (Hwf : well_founded r) (k : Nat) : well_founded r :=
  well_founded.intro
  (Nat.rec_on k
     (λ n : A, well_founded.apply Hwf n)
     (λ (k' : Nat) (f : Π a, acc r a), (λ n : A, acc.intro n (λ y H, f y))))

end well_founded
