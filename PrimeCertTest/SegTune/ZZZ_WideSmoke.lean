/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does a window of 8388608 bits run at all

No width but 4194304 has ever been run, so before a timing pair is queued at twice that, this asks
the cheap question: a wide window over a couple of thousand divisors and a small base. Every one of
those divisors is deep in the band whose mask is built to the window's width, which is the part of
the run the width changes most. Throwaway. -/

namespace PrimeCert.SegTune.ZZZ_WideSmoke

run_segment 100000000000001 8388608 2000 8192 1000000

end PrimeCert.SegTune.ZZZ_WideSmoke
