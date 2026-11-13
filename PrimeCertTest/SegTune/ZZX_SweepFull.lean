/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole design in one arm

`parts 11`: the marking route over the marked subset **and** the gcd equations over the skipped
set, with the strike set swept from the wide band and no self-check. This is the shape production
would take, short of the chain tying the gcds to `segLoopK`.

Why this and not the sum of `ZZV_WideSweepNoCheck` and `ZZW_SweepGcdOnly`: they share work, and
adding them counts it twice. `ZZW` builds the finished window because its gcds are stated over it,
`ZZV` does not build it at all, and both run the small-band base and the sweep. So the sum is an
overestimate by at least one window build, and the only way to know the real figure is to run the
combination.

Against `ZZH_FullWindow28`, one job, peak each. The comparison that matters:

* `ZZV` already beats `ZZH` on all three, kernel −32%, processor −17%, peak −5%, while proving
  nothing about the 435226 skipped divisors.
* This arm pays for proving it. If it still beats `ZZH`, the design is worth the proof work, and
  `project_window_sieve_tuning` has the four lemmas that chain it.
* If it does not, the saving exists only while nothing is proved, and that is worth knowing
  plainly rather than discovering after the proof is written.

Read the `skip gcds` column apart from the batch lemmas, as always.

Throwaway. -/

namespace PrimeCert.SegTune.ZZX_SweepFull

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 11 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZX_SweepFull
