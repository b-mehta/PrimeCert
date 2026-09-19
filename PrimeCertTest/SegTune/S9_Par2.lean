/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The second of four consecutive segments run at once

The stretch after `S9_Par1`, which is where that file's segment ends. -/

namespace PrimeCert.SegTune.S9_Par2

run_sieve 10000000

run_segment_variant 28 100000012582913 4194304 3333332 16384 10000000

end PrimeCert.SegTune.S9_Par2
