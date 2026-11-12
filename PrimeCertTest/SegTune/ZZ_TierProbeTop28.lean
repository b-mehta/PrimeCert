/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Is the top-tier variant live

Mode 28 over divisors that reach past base index 700000, which is where the schedule stops using
`batchLen` and falls through to the call's own length. A narrow window, because the tier boundary
is an index and does not depend on the width, so this costs little.

Pair with `ZZ_TierProbeTop83` and **compare the batch lemma counts**: above 700000 mode 28 takes
the call's 2048 and mode 83 takes 1536, so mode 83 must report more batches. Equal counts would
mean mode 83 is inert, as 84 and 85 were. Throwaway. -/

namespace PrimeCert.SegTune.ZZ_TierProbeTop28

run_sieve 10000000

run_segment_variant 28 100000000000001 65536 750000 2048 10000000

end PrimeCert.SegTune.ZZ_TierProbeTop28
