/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Tree dispatch deriving only the two strikes this band has

`E4_TreeW` ran the tree over the divisors whose double already passes the end of the segment, and
lost 4.9 percent of kernel to `Q7_Sorted` while saving 8.8 percent of peak. It derived eight
strikes a divisor and threw six away, which is what that band's guard does with them.

This derives two. If the loss was the wasted six, it should come back; if it does not, the tree
costs more than records here for some other reason and the design stays split by band. -/

namespace PrimeCert.SegTune.E4_TreeW2

run_sieve 10000000

run_segment_variant 43 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.E4_TreeW2
