/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A small segment through the tree route, to check the route before timing it

Mode 45 over a window small enough to settle in seconds. Nothing here is a measurement: it exists
so that a wrong assembled mask or a mismatched hypothesis fails here rather than in a job. -/

namespace PrimeCert.SegTune.E2_TreeSmoke

run_segment_variant 45 1000000001 524288 33334 1536

end PrimeCert.SegTune.E2_TreeSmoke
