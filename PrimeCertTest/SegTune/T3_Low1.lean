/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The first window of a pair sieved by the divisors a mid-range window needs

`S9_Par1` and `S9_Par2` are the two windows a runner takes at once, each sieved by every divisor to
10^7, which only the topmost window of 1..10^14 needs. This pair halves that to the count a window
near 2.5e13 needs, so timing the two pairs against each other measures the saving that
`scripts/fuel_by_window.py` has so far only counted. -/

namespace PrimeCert.SegTune.T3_Low1

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 1666666 8192 10000000

end PrimeCert.SegTune.T3_Low1
