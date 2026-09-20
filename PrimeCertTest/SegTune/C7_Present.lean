/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A ten million base present in the environment and referenced by nothing

`C7_Base1e7` against `C7_B1e6` found the batch lemmas about four percent slower beside a ten times
larger base, in both rounds, although those lemmas never mention the base and the two arms emit the
same statements over the same divisors. The only emitted statements that do mention it, the slice
lemmas, carry one percent of the gap.

This arm builds the ten million sieve and then runs the segment against the million, so the larger
literal sits in the environment and no emitted declaration refers to it. Read as three:
`C7_B1e6` has it absent, this has it present and unused, `C7_Base1e7` has it present and used. If
this matches `C7_Base1e7` the cost follows presence; if it matches `C7_B1e6` it follows use. -/

namespace PrimeCert.SegTune.C7_Present

run_sieve 10000000

run_segment_variant 20 100000000000001 4194304 333333 1536 1000000

end PrimeCert.SegTune.C7_Present
