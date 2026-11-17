/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `10^8` base at a batch length of 64

`S8_Sieve1e8` is the same bound at the default 16. Asked because 64 is worth 3.65 GiB to a whole
window at `10^17` and the length is a per-call argument, so whether `run_sieve`'s default of 16
should move needs a reading at the bound `10^16` uses as well as the one `10^17` does.

The cliff moves with the bound — 256 was killed at `3.163 * 10^8` and 64 at `10^9` — so a length
that wins at the larger bound is not assumed to win at the smaller.

Throwaway. -/

namespace PrimeCert.SegTune.S23_Base1e8Len64

run_sieve 100000000 64

end PrimeCert.SegTune.S23_Base1e8Len64
