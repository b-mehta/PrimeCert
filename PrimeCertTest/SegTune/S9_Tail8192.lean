/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted run with 8192 positions to a batch over the large primes

Between 2048 and 4096 the run's time did not move and its peak memory fell, so this file and
`S9_Tail16384` carry the same question further, which an entry of 16 bits allows. -/

namespace PrimeCert.SegTune.S9_Tail8192

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.S9_Tail8192
