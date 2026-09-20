/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One file of 24 gap-walked segments, to be timed alone and beside three others

How much a segment costs when four files share a runner, against what it costs when one file has
the runner to itself. Both figures have been measured before but never in the same job, and a
ratio of two ratios taken on different runners is as unsafe as comparing raw seconds across them:
the same four files took 794 s on one runner and 1144 s on another the same night. `QAll` imports
this and `Q1` to `Q3`, and the `onefour` job alternates one against four on one runner.
-/

namespace PrimeCert.Q0

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 24 15

end PrimeCert.Q0
