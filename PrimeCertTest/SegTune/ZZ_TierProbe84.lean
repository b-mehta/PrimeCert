/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The bottom tier moved, over divisors that are all in it

Mode 84 against `ZZ_TierProbe28`. The reasoning is there; the short version is that the batch
lemma count must fall by about four fifths, and if it does not the variant never reached the loop
the banded run uses. Throwaway. -/

namespace PrimeCert.SegTune.ZZ_TierProbe84

run_segment_variant 84 100000000000001 262144 20000 2048 1000000

end PrimeCert.SegTune.ZZ_TierProbe84
