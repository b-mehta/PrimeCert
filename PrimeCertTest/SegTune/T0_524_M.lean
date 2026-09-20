/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Ten billion, 524288 positions, marked

The comparison arm for `T0_524_S`. -/

namespace PrimeCert.SegTune.T0_524_M

run_segment_variant 20 10000000001 524288 33334 1536

end PrimeCert.SegTune.T0_524_M
