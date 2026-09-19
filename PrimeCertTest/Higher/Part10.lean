/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `4780843265`, part eleven of twelve (see `Higher.Part00`) -/

namespace PrimeCert.Higher.P10

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 4780843265 524288 100003 20 2048 1536 240 7

end PrimeCert.Higher.P10
