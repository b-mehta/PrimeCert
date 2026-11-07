/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same segment with the two middle bands in batches of 4096

`S9_Par1` runs the divisors striking the window four or eight times in batches of 512 and 768.
Those tiers were set when four files shared a runner; two files now hold 7.67 GB summed. A
September measurement on a real certificate put 4096 at 10 percent of kernel below the short
tiers and was rejected on the memory ceiling of the time. -/

namespace PrimeCert.SegTune.M2_MidLong

run_sieve 10000000

run_segment_variant 57 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.M2_MidLong
