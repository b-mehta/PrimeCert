/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Ten billion, 1048576 positions, sorted

The third of the four widths, and the one that won at a trillion. -/

namespace PrimeCert.SegTune.T0_1M_S

run_segment_variant 28 10000000001 1048576 33334 1536

end PrimeCert.SegTune.T0_1M_S
