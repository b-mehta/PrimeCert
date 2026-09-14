/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Segment timing baseline: the sieve to `10^7` alone

Every case with divisors up to `10^7` builds this sieve first, so subtracting this file's time
leaves the segment's own cost. -/

namespace PrimeCert.SegTune.S7_Sieve

run_sieve 10000000

end PrimeCert.SegTune.S7_Sieve
