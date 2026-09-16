/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: mode 11

`V7_M3` with the batch literals computed by the `segLoopC` twin, which clamps the crossing-out
pattern to the window and reads the base primes from the batch's own slice. The kernel sees exactly
what `V7_M3` gives it, so the pair measures the command's own computation. -/

namespace PrimeCert.SegTune.V7_M11

run_sieve 10000000

run_segment_variant 11 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.V7_M11
