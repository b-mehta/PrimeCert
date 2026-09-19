/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A whole run whose large primes are sorted into slices

`S7_Sched` with one change: a batch every one of whose primes is bigger than half the segment, so
that each hits the segment at most twice, is settled by sorting those hits into slices of the
segment rather than by marking the segment once per prime. Same segment, same divisors, same
emitted statements, so the pair is the change on its own. -/

namespace PrimeCert.SegTune.S9_Stripes

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.S9_Stripes
