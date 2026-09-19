/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One slice's worth of the work, over the divisors below half the segment

The same walk over the same divisors as `N7_M18`, those at wheel indices 1 to 700416, whose
multiples land in the segment many times each; but each one's multiples are written into a single
65536-bit piece of the segment rather than into a number as wide as the whole segment. Covering the
segment would need all 64 pieces, so this file against `N7_M18` says whether working a piece at a
time could pay at all: it can only pay if this is under a sixty-fourth of that. No chain and no
final theorem in either. -/

namespace PrimeCert.SegTune.N7_M24

run_sieve 10000000

run_segment_variant 24 100000000000001 4194304 700416 1536 10000000

end PrimeCert.SegTune.N7_M24
