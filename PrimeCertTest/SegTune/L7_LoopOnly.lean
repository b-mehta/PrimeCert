/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The command's own computation alone

The same segment and the same divisors as `V7_M11`, with the command running its loop and emitting
one number at the end. Its peak against `V7_M11`'s under `debug.skipKernelTC` separates the loop's
own footprint from the 2171 literals the emitted statements hold. -/

namespace PrimeCert.SegTune.L7_LoopOnly

run_sieve 10000000

run_segment_variant 19 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.L7_LoopOnly
