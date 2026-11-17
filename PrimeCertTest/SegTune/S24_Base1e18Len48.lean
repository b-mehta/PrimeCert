/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `10^9` base at a batch length of 48

The last length left between the two behaviours at this bound. 32 accumulated for 9:43 and was
killed at 14298800 KiB; 64 was killed at 14015780 after 25 seconds, which is the other shape
entirely. Below 32 the readings are flat: 16 gave 14465364, 8 gave 14316404 and 4 gave 14272748,
all killed.

Throwaway. -/

namespace PrimeCert.SegTune.S24_Base1e18Len48

run_sieve 1000000000 48

end PrimeCert.SegTune.S24_Base1e18Len48
