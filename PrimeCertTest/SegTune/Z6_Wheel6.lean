/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One window of the wheel of six, at the divisor count a 1..10^12 run needs

The batch equations of a 4194304-bit window and nothing else: no chain and no soundness, so what
is timed is the marking. `Z7_Wheel30` is the same width and the same divisors on the wheel of
thirty, where a bit stands for 3.75 integers rather than 3, so that window reaches a quarter
further for the same divisor work. Whether that costs more per divisor, since a divisor there has
eight progressions rather than two, is the question. Run the pair alternated on one machine and
compare kernel seconds; the wheel of thirty wins only if it is under 1.25 times this. -/

namespace PrimeCert.SegTune.Z6_Wheel6

run_wheel 6 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.Z6_Wheel6
