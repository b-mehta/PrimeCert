/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One sieved sum, from the emitted pieces end to end

The bound is 101 and the height is the top of a sieved segment above 10201. The range splits as
the three stretches the leaf lemmas cover: nothing survives at or below 101, the survivors from
102 to 10200 are the primes there, which is the difference of two base runs, and above 10201 the
sieved segments answer.
-/

namespace PrimeCert.PhiConcrete

run_harmonic 10200 20 256

run_harmonic 101 20 256

/-- The survivors from 102 to 10200, which are the primes there, as the difference of the two runs
above. The two totals and the two counts are the numerals those runs printed. -/
theorem mid :
    SievedRecipRange 102 10201 101 67261737454004311175 1274 (10 ^ 20) :=
  sievedRecipRange_of_two_icc (B := 101) (N := 10200) (by omega) (by omega) (by omega)
    primeRecipIcc_10200_20_256 primeRecipIcc_101_20_256 (by rfl) (by rfl)

run_segment_variant 20 10201 1024 33 1536

set_option maxRecDepth 400000 in
run_sieved_segment 10201 1024 101 20 256 1536

/-- The three stretches joined: nothing to 101, the primes to 10200, the sieved segment to 13271.
Totals and counts add as literals. -/
theorem whole :
    SievedRecipRange 5 13273 101 70134779872703497807 1610 (10 ^ 20) :=
  sievedRecipRange_add (b := 10201) (by rfl) (by rfl)
    (sievedRecipRange_add (b := 102) (A := 67261737454004311175) (C := 1274) (by rfl) (by rfl)
      (sievedRecipRange_below (by omega)) mid (by rfl) (by rfl))
    sievedRecipRange_10201_1024_101_20 (by rfl) (by rfl)

/-- The sieved sum itself, read off that range: the numbers up to 13272 with no prime factor at or
below 101 have reciprocals summing into this interval. -/
theorem value :
    phiB 13272 101 ∈ Set.Icc
      ((170134779872703497807 : ℚ) / 10 ^ 20) ((170134779872703499417 : ℚ) / 10 ^ 20) :=
  phiB_mem_Icc_of_range_scaled (by omega) (by omega) (by rfl) whole (by rfl) (by rfl)

end PrimeCert.PhiConcrete
