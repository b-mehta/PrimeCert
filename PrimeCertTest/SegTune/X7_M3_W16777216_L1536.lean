/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: mode 3, window 16777216 bits, batches of 1536 steps

Mode 3 at four times the window of `V7_M3`. The same window under mode 0 was killed above 14 GB.
Builds the sieve to `10^7` first (`S7_Sieve` times that alone). -/

namespace PrimeCert.SegTune.X7_M3_W16777216_L1536

run_sieve 10000000

run_segment_variant 3 100000000000001 16777216 3333332 1536 10000000

end PrimeCert.SegTune.X7_M3_W16777216_L1536
