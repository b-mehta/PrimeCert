/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The full divisor range, the top point of the fuel series

A segment walks `fuel` wheel positions to find the primes among them, and each prime it finds
places its strikes. `D1_Fuel333333` to `D1_Fuel3333332` hold the window fixed and vary only how
many positions are walked, so the series separates what the walk costs from what the strikes cost.
Only this arm is a correct sieve for 10^14; the shorter ones are measurements, not certificates. -/

namespace PrimeCert.SegTune.D1_Fuel3333332

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.D1_Fuel3333332
