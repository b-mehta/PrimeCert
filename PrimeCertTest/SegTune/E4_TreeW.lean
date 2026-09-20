/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Tree dispatch over the divisors that strike the segment at most twice

The tree beat the sorted records over the eight-strike band. This is the other end: divisors whose
double already passes the end of the segment, where each progression is hit once and sorting needs
only two records.

`treeDivK` always derives eight strikes from a divisor, so here six of them land past the window's
end and are thrown away by the guard in `putK`. That is six derivations and six tests wasted per
divisor, against two records the sorted route never builds, so the result need not follow the
eight-strike band's. Against `Q7_Sorted`, which runs mode 25 over the same divisors. -/

namespace PrimeCert.SegTune.E4_TreeW

run_sieve 10000000

run_segment_variant 42 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.E4_TreeW
