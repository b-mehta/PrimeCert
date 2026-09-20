/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted run with 16384 positions to a batch over the large primes

The far end of the sweep that `S9_Tail4096` and `S9_Tail8192` sit on. Above 32768 an entry would
not fit its 16 bits. -/

namespace PrimeCert.SegTune.S9_Tail16384

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 16384 10000000

end PrimeCert.SegTune.S9_Tail16384
