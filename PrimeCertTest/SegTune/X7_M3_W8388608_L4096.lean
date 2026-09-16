/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: mode 3, window 8388608 bits, batches of 4096 steps

Mode 3 at twice `V7_M3`'s window and nearly three times its batch length (814 batch lemmas).
Builds the sieve to `10^7` first. -/

namespace PrimeCert.SegTune.X7_M3_W8388608_L4096

run_sieve 10000000

run_segment_variant 3 100000000000001 8388608 3333332 4096 10000000

end PrimeCert.SegTune.X7_M3_W8388608_L4096
