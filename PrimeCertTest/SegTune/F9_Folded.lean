/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same run with a batch's two theorems emitted as one

Handing each batch its own round count made a sorted batch contribute two theorems rather than
one: the sorted batch itself, and that batch restated for the unclamped loop the chain runs
through. This file passes the first straight into the second instead of naming it, which is one
declaration a batch fewer and the same statements reaching the chain. Four segments at once are
CPU-bound on elaboration rather than on the kernel, so that is what this asks about. -/

namespace PrimeCert.SegTune.F9_Folded

run_sieve 10000000

run_segment_variant 38 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.F9_Folded
