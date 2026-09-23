/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole segment with every batch settled by a mask built by doubling

`S9_Par1` sorts each divisor's strikes into records for the three bands where a divisor strikes at
most eight times. This settles every batch the way the small divisors are settled, by a mask of
period `2p` built by repeated doubling. Sorted against marked has been compared before only by
band probes, which are now known to disagree with a real run, so this is that comparison over a
certificate. -/

namespace PrimeCert.SegTune.D2_Marked

run_sieve 10000000

run_segment_variant 56 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.D2_Marked
