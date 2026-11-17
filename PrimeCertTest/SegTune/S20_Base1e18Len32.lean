/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `10^9` base at a batch length of 32

`S10_Sieve1e18Base` is the same bound at the default 16, and it was killed at 14465364 KiB, which
is what closed `10^18` here. Lengths of 8 and 4 moved that peak 0.75%, so the knob looked spent.

Upward it is not. At the `3.163 * 10^8` bound a length of 64 took the peak from 6707116 to
5737748 KiB for the same kernel time, 14.5% less, while 256 was killed in twelve seconds. This
and its two companions ask whether the bound `10^18` needs comes under the limit somewhere in
between.

Throwaway. -/

namespace PrimeCert.SegTune.S20_Base1e18Len32

run_sieve 1000000000 32

end PrimeCert.SegTune.S20_Base1e18Len32
