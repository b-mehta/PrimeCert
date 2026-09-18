/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # Two windows above `10 ^ 12`

One of twelve files built at once, so that the cost of a window in a real run can be compared with
the cost of the same window timed on its own. `Shape.All` pulls the twelve together.
-/

namespace PrimeCert.Shape.P00

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000013 20 2048 1536 2 1

end PrimeCert.Shape.P00
