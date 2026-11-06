/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One segment summed by walking positions rather than dividing

Form 16 emits each batch as a walk that adds the position it reaches, takes the count from the
walk's own gaps, and encloses the segment from those two numbers through the offset expansion.
The range theorem it proves has the same shape as form 15's, so the two are interchangeable in a
run and can be timed against each other.
-/

namespace PrimeCert.GapAB.Form16

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 65536 100003 20 2048 1536 1 16

end PrimeCert.GapAB.Form16
