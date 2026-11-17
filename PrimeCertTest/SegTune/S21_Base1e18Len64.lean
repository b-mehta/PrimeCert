/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `10^9` base at a batch length of 64

The middle arm of the sweep `S20_Base1e18Len32` describes, and the length that won at the
`3.163 * 10^8` bound.

Throwaway. -/

namespace PrimeCert.SegTune.S21_Base1e18Len64

run_sieve 1000000000 64

end PrimeCert.SegTune.S21_Base1e18Len64
