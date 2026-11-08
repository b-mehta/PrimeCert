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

/-! Four neighbouring windows of the same sieve, joined into one range. The join adds the totals
and the counts as literals, so the four windows become a single enclosure covering 100001 up to
the end of the fourth. -/

run_segment_variant 20 103073 1024 33 1536

set_option maxRecDepth 400000 in
run_sieved_segment 103073 1024 101 20 256 1536

run_segment_variant 20 106145 1024 33 1536

set_option maxRecDepth 400000 in
run_sieved_segment 106145 1024 101 20 256 1536

run_segment_variant 20 109217 1024 33 1536

set_option maxRecDepth 400000 in
run_sieved_segment 109217 1024 101 20 256 1536

run_sieved_join 100001 1024 101 20 4

/-! The same four windows as running totals rather than one join, so a height at any window's end
has a statement of its own. -/

run_sieved_prefix 100001 1024 101 20 4

end PrimeCert.SievedLeaf
