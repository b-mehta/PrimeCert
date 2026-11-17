/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `3.163 * 10^8` base at a batch length of 128

The gap in the sweep: 64 took the peak from 6707116 to 5737748 KiB and 256 was killed in twelve
seconds, so whether anything is left between them is unread. At the `10^9` bound the same cliff
arrives sooner, with 64 and 128 killed inside half a minute, which is why this is asked at the
bound `10^17` needs rather than there.

Throwaway. -/

namespace PrimeCert.SegTune.S19_Base1e17Len128

run_sieve 316300000 128

end PrimeCert.SegTune.S19_Base1e17Len128
