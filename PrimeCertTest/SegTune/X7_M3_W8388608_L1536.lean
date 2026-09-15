/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: mode 3, window 8388608 bits, batches of 1536 steps

Mode 3 at twice the window of `V7_M3`, which peaked at 8.7 GB, so this size may now fit a 16 GB
runner. Builds the sieve to `10^7` first (`S7_Sieve` times that alone). -/

namespace PrimeCert.SegTune.X7_M3_W8388608_L1536

run_sieve 10000000

run_segment_variant 3 100000000000001 8388608 3333332 1536 10000000

end PrimeCert.SegTune.X7_M3_W8388608_L1536
