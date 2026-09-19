/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One segment at ten billion, sorted

A segment of 262144 positions starting at 10000000001, crossed out by the divisors up to 100003,
which is just above the square root of the segment's top and so is the bound at which a survivor is
certified prime. Four pieces of 65536 rather than the 64 the wider segments use.

This height and the one in `H1_Sorted` are what the prime reciprocal sum session needs sieved to
reach 10^16 by the method of Bach, Klyve and Sorenson, which asks for the primes to x^(2/3) rather
than to x. `H0_Marked` is the same segment marked the way the sieve does today. -/

namespace PrimeCert.SegTune.H0_Sorted

run_sieve 1000000

run_segment_variant 28 10000000001 262144 33334 1536 1000000

end PrimeCert.SegTune.H0_Sorted
