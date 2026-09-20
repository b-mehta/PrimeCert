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
width, which is what the other session has at its own width and I did not.

The base sieve stays the one in `PrimeCert/SieveBase.lean`, because `run_segment_variant` looks its
base up by exact name rather than by which cache covers the range; `fuel` is what sets how many
divisors the run uses, and 33333 stops it at the last index below a hundred thousand. -/

namespace PrimeCert.SegTune.C7_B1e5

run_segment_variant 20 100000000000001 4194304 33333 1536 1000000

end PrimeCert.SegTune.C7_B1e5
