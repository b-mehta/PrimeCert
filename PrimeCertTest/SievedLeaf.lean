/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A leaf window sitting far above the square of its bound

1024 wheel positions from 100001, sieved by the primes to 101. The window runs to about 300000,
where the square of the bound is 10201, so `run_harmonic_segment` refuses this window: a bit of it
says only that the number has no prime factor at or below 101. `run_sieved_segment` states the
enclosure of the sieved sum, which holds at any height, and this file is the check that it does.
-/

namespace PrimeCert.SievedLeaf

run_segment_variant 20 100001 1024 33 1536

set_option maxRecDepth 400000 in
run_sieved_segment 100001 1024 101 20 256 1536

end PrimeCert.SievedLeaf
