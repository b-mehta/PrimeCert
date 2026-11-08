/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

import Mathlib.Tactic.NormNum.Prime

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

/-! ## One step of the expansion, on these numbers

Splitting at 103 takes the value at bound 102 and the value at bound 102 of the quotient 13272 by
103, which is 128, to the value at bound 103. The quotient's own range needs one more base run. -/

run_harmonic 128 20 256

/-- The quotient's range: the survivors from 102 to 128, again a difference of two base runs. -/
theorem quotMid :
    SievedRecipRange 102 129 101 4495241745336192858 53 (10 ^ 20) :=
  sievedRecipRange_of_two_icc (B := 101) (N := 128) (by omega) (by omega) (by omega)
    primeRecipIcc_128_20_256 primeRecipIcc_101_20_256 (by rfl) (by rfl)

/-- The quotient's whole range, with the empty stretch below 102 joined on. -/
theorem quotWhole :
    SievedRecipRange 5 129 101 4495241745336192858 53 (10 ^ 20) :=
  sievedRecipRange_add (b := 102) (A := 4495241745336192858) (C := 53) (by rfl) (by rfl)
    (sievedRecipRange_below (by omega)) quotMid (by rfl) (by rfl)

/-- The quotient's value at bound 101. -/
theorem quotValue :
    phiB 128 101 ∈ Set.Icc
      ((104495241745336192858 : ℚ) / 10 ^ 20) ((104495241745336192911 : ℚ) / 10 ^ 20) :=
  phiB_mem_Icc_of_range_scaled (by omega) (by omega) (by rfl) quotWhole (by rfl) (by rfl)

/-- The only number above 101 and at most 102 is 102, which is composite. -/
theorem hno102 : ∀ q, 101 < q → q ≤ 102 → ¬ q.Prime := by
  intro q h1 h2
  have : q = 102 := by omega
  subst this
  norm_num

/-- Splitting at 103. Both children move up to bound 102 first, which changes nothing since 102 is
composite, and the two quotients carry the division by 103. -/
theorem valueAt103 :
    phiB 13272 103 ∈ Set.Icc
      ((169120262962554602730 : ℚ) / 10 ^ 20) ((169120262962554604341 : ℚ) / 10 ^ 20) :=
  phiB_mem_Icc_split (p := 103)
    (Qhi := 1014516910148895077) (Qlo := 1014516910148895076) (by norm_num) (by rfl)
    (phiB_mem_Icc_of_no_primes (B' := 101) (by omega) hno102 value)
    (phiB_mem_Icc_of_no_primes (B' := 101) (by omega) hno102 quotValue)
    (by rfl) (by rfl) (by rfl) (by rfl)

end PrimeCert.PhiConcrete
