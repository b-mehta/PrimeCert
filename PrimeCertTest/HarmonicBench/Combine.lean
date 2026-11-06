/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.PrimeHarmonic
public meta import PrimeCert.Meta.QuickRfl

/-! # Joining the four pieces of the record run into one enclosure

The record run proves one interval enclosure up to `10 ^ 8` and three ranges above it, each in its
own job. `combine` takes those four statements as hypotheses and concludes the enclosure up to
20635312384, so the only arithmetic outside the four jobs is the kernel's addition of the eight
literals. The scale is `10 ^ 20` throughout.
-/

namespace PrimeCert

/-- The four pieces of the record run, added. -/
public theorem combine
    (h₁ : PrimeRecipIcc 100000000 234164189658716328899 5761453 100000000000000000000)
    (h₂ : PrimeRecipRange 100000001 1005969665
      11806779523140848021 45374243 100000000000000000000)
    (h₃ : PrimeRecipRange 1005969665 10820641025
      10849165638201014977 3271557120 100000000000000000000)
    (h₄ : PrimeRecipRange 10820641025 20635312385
      2755666357653066352 3271557120 100000000000000000000) :
    PrimeRecipIcc 20635312384 259575801177711258249 6594249936 100000000000000000000 := by
  have k₁ : PrimeRecipIcc 1005969664 245970969181857176920 51135696 100000000000000000000 :=
    primeRecipIcc_add_range (by quickRfl) h₁ h₂ (by quickRfl) (by quickRfl)
  have k₂ : PrimeRecipIcc 10820641024 256820134820058191897 3322692816 100000000000000000000 :=
    primeRecipIcc_add_range (by quickRfl) k₁ h₃ (by quickRfl) (by quickRfl)
  exact primeRecipIcc_add_range (by quickRfl) k₂ h₄ (by quickRfl) (by quickRfl)

end PrimeCert
