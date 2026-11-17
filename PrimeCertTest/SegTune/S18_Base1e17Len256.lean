/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `3.163 * 10^8` base at a batch length of 256

The long arm of the sweep `S17_Base1e17Len64` describes, against `S9_Sieve1e17Base` at the default
16. Fuel is 5928 steps here, so 256 leaves 24 batches where the default leaves 371.

Throwaway. -/

namespace PrimeCert.SegTune.S18_Base1e17Len256

run_sieve 316300000 256

end PrimeCert.SegTune.S18_Base1e17Len256
