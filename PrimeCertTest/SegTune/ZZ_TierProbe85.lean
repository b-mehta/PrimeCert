/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The boundaries moved, checked the same way

Mode 85 against `ZZ_TierProbe28`. At this window the first band edge is at index 10922 where the
schedule's first tier ends at 20000, so the count must sit between the two tier counts rather than
matching either. Throwaway. -/

namespace PrimeCert.SegTune.ZZ_TierProbe85

run_segment_variant 85 100000000000001 262144 20000 2048 1000000

end PrimeCert.SegTune.ZZ_TierProbe85
