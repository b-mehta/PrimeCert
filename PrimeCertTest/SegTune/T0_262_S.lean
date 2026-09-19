/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Ten billion, 262144 positions, sorted

The first of four widths at a start of 10000000001 with divisors to 100003 throughout. This repeats
at ten billion the sweep that `V262_Sorted` and its neighbours did at one trillion, since the range
that has to be sieved to reach 10^16 is made mostly of decades below a hundred billion.

These are timing files. The divisor bound is held fixed across the four widths so that only the
width moves, which means it does not clear the square of the top of the widest of them; a run that
wanted the survivors certified prime would raise it. -/

namespace PrimeCert.SegTune.T0_262_S

run_segment_variant 28 10000000001 262144 33334 1536

end PrimeCert.SegTune.T0_262_S
