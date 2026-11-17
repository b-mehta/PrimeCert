/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `10^9` base at a batch length of 128

The long arm of the sweep `S20_Base1e18Len32` describes. At the `3.163 * 10^8` bound 256 was
killed in twelve seconds and 64 was the best of the three tried, so this is the side of 64 nobody
has a reading for.

Throwaway. -/

namespace PrimeCert.SegTune.S22_Base1e18Len128

run_sieve 1000000000 128

end PrimeCert.SegTune.S22_Base1e18Len128
