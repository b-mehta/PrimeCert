/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One window above `10 ^ 8`, with the bit test as it stands

The reference arm for the bit test comparison, cut to one window so that many rounds fit in a job.
-/

namespace PrimeCert.Bitn1e8.F1

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 262144 31721 20 2048 1536 1 1

end PrimeCert.Bitn1e8.F1
