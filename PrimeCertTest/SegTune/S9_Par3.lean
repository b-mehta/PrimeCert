/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The third of four consecutive segments run at once

The stretch after `S9_Par2`, which is where that file's segment ends. -/

namespace PrimeCert.SegTune.S9_Par3

run_sieve 10000000

run_segment_variant 28 100000025165825 4194304 3333332 8192 10000000

end PrimeCert.SegTune.S9_Par3
