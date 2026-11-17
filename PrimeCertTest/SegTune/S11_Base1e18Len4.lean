/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The `10^9` base in shorter batches

`S10_Sieve1e18Base` with the batch length at 4 sieving steps rather than the default 16, so the
chain is checked in four times as many declarations.

`run_sieve n len` already takes that length, and shortening it is the same checkpointing that the
metaprogramming notes describe: a chain split into more declarations has a peak that follows one
batch rather than the whole fold. The base at `10^9` was killed at 14465364 KiB against a
14000000 KiB limit, so it is over by an amount nobody has measured, and this asks whether the knob
that already exists closes it.

The notes also say the trade is not monotone, that time fell with more stages while memory was
U-shaped. So 4 is one point and 8 is the other, and either may be worse than 16.

Pair with `S12_Base1e18Len8` and `S10_Sieve1e18Base`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.S11_Base1e18Len4

run_sieve 1000000000 4

end PrimeCert.SegTune.S11_Base1e18Len4
