/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Four windows of the billion run

`Billion.Part00` with four windows in place of ninety-six, so that a change to the fold or the
segment can be timed in a minute rather than ten. -/

namespace PrimeCert.Bench.H4

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 4

end PrimeCert.Bench.H4
