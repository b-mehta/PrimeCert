/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does a schedule variant reach the banded loop at all

Mode 28 over divisors that all fall in the schedule's bottom tier, so that every batch takes its
length from that tier and nothing else. Pair with `ZZ_TierProbe84`, which is mode 84 over the same
divisors, and **compare the batch lemma counts, not the seconds**: the bottom tier goes from 256 to
1024, so the count must fall by about four fifths. If the two counts agree, the variant is inert.

That is not hypothetical. Modes 84 and 85 were first wired into the schedule site in the branch a
non-banded mode uses, which a banded run never reaches, and the full-divisor pair came back a tie
with both arms reporting 1469 batch lemmas. The count is what gave it away. Throwaway. -/

namespace PrimeCert.SegTune.ZZ_TierProbe28

run_segment_variant 28 100000000000001 262144 20000 2048 1000000

end PrimeCert.SegTune.ZZ_TierProbe28
