/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PhiLadder
public meta import PrimeCert.SegmentedSieve

/-! # One sweep carried up through a run of bounds

The window of 1024 positions from 100001 is sieved once to 101, then carried to every prime up to
151 by a rung each. Each rung's equation is checked by the kernel against the steps between its
bound and the one below, so the sieving is done once rather than once per bound.
-/

namespace PrimeCert.SegLadderTest

run_segment_variant 20 100001 1024 33 1536

set_option maxRecDepth 400000 in
run_segment_ladder 100001 1024 33 1536 151 20

end PrimeCert.SegLadderTest
