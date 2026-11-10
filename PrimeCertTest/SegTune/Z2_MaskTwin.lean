/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The window after a batch, found through a mask per divisor

One window at the divisor count a 1..10^12 run needs, the same as `WA_Narrow`. This is the older of the two
routes, kept under mode 66: an unsorted batch settles what the window looks like after it by
building a mask for each divisor and subtracting it, which is `segLoopC`, reported under that name
by `run.sh`. `Z3_BytesTwin` is the default, reaching the same literal through a byte array; the
kernel checks the literal either way, so the pair prices the route and nothing else. Measured
alternated on a quiet 32 vCPU box: this arm 110.5, 112.9 and 112.0 processor seconds against the
other's 87.7, 85.7 and 85.6. -/

namespace PrimeCert.SegTune.Z2_MaskTwin

run_sieve 10000000

run_segment_variant 66 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.Z2_MaskTwin
