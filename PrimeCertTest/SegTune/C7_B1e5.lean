/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A third bound at the same width

`S7_Sched` and `C7_B1e6` are the same segment and shape with divisors to ten million and to one
million. This is the same again at a hundred thousand, so the three give a bound series at one
width, which is what the other session has at its own width and I did not. The cache in
`PrimeCert/SieveBase.lean` already covers this range, so no `run_sieve` is needed. -/

namespace PrimeCert.SegTune.C7_B1e5

run_segment_variant 20 100000000000001 4194304 33333 1536 100000

end PrimeCert.SegTune.C7_B1e5
