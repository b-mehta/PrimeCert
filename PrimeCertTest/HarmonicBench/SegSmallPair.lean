/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Two neighbouring windows above a sieve, summed and joined

The same setting as `SegSmall`: dividing by the primes up to `101`, windows of 300 wheel positions.
The first covers `707` to `1603`, the second `1607` to `2503`, and the join covers both. Their
counts must add to the number of primes from `707` to `2503`.
-/

namespace PrimeCert.SegPair

run_segment 707 300 33 8

run_segment 1607 300 33 8

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 707 300 101 12 64 8

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 1607 300 101 12 64 8

run_harmonic_join 707 300 101 12 2

end PrimeCert.SegPair
