/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.PrimeHarmonic

public meta import PrimeCert.Meta.Sieve
meta import PrimeCert.Meta.QuickRfl

/-! # One batch low in the `5 * 10 ^ 7` sieve

Positions 1000 to 5999, numbers up to 17999, 1634 of them prime. The same length as
`Height5e7Mid` and `Height5e7High`, so the three differ only in how far up the sieve they read.
-/

namespace PrimeCert.Sieve

run_sieve 50000000

end PrimeCert.Sieve

namespace PrimeCert

set_option maxRecDepth 4000000 in
set_option Elab.async false in
theorem height5e7Low :
    Nat.beq (sumB (recipAtK Sieve.sieveBits_50000000 100000000000000000000) 1000 5000 1)
      20045868165642763437 = true := by
  quickRfl

end PrimeCert
