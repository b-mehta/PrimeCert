/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.PrimeHarmonic

public meta import PrimeCert.Meta.Sieve
meta import PrimeCert.Meta.QuickRfl

/-! # One batch at the top of the `5 * 10 ^ 7` sieve

Positions 16660000 to 16664999, numbers up to 49994999, 829 of them prime. The same length as
`Height5e7Low` and `Height5e7Mid`.
-/

namespace PrimeCert.Sieve

run_sieve 50000000

end PrimeCert.Sieve

namespace PrimeCert

set_option maxRecDepth 4000000 in
set_option Elab.async false in
theorem height5e7High :
    Nat.beq (sumB (recipAtK Sieve.sieveBits_50000000 100000000000000000000) 16660000 5000 1)
      1658419426457626 = true := by
  quickRfl

end PrimeCert
