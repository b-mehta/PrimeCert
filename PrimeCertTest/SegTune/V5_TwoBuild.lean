/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Two consecutive windows' small-band masks, each built by doubling

One arm of a pair. `V6_TwoShift` states the same quantity with the second window's mask taken
from the first by a shift, so the difference between them is what sharing a divisor's
construction across windows is worth. -/

namespace PrimeCert.SegTune.V5_TwoBuild

run_sieve 10000000

run_segment_variant 64 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.V5_TwoBuild
