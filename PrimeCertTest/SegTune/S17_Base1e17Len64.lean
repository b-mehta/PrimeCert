/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `3.163 * 10^8` base at a batch length of 64

`S9_Sieve1e17Base` is the same bound at the default 16. The phase log says the base's memory
accumulates over the chain's batches rather than appearing at the end: 371 batches of 16 took it
from 1045 MiB at batch 0 to 6533 at the last, each batch adding a step theorem whose statement
carries two literals the width of the whole sieve.

A longer batch makes fewer of those and asks the kernel for more per check. Which way that comes
out is what this and `S18_Base1e17Len256` are for. Only lengths below the default have been tried
before, at the `10^9` bound, where 16, 8 and 4 moved the peak by 0.75%.

Throwaway. -/

namespace PrimeCert.SegTune.S17_Base1e17Len64

run_sieve 316300000 64

end PrimeCert.SegTune.S17_Base1e17Len64
