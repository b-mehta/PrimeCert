/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The wide band at today's record format

Mode 31: the band whose divisors have their double past the end of the window, sorted at two
records a divisor in the three-bit lane format the production route uses. 8192 is not a choice
here, it is the most that format holds, since three bits name the strike and thirteen the position.

This is the control. Pair it with `ZZE_WideOne86`, **both arms in one job**, and report peak for
each. Boxes of the same type have come back 161 s to 226 s on the same file, so no second measured
here may be carried across to a number measured anywhere else.

Read it on windows per machine-hour rather than seconds: the two arms differ in how many batches
cover the same band, so they differ in memory as well as time, and the packing has to come from a
measured marginal rather than either arm's own peak.

Throwaway. -/

namespace PrimeCert.SegTune.ZZD_WideCtl31

run_sieve 10000000

run_segment_variant 31 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZD_WideCtl31
