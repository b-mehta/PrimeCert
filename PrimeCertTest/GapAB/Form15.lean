/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The same segment summed by dividing, for the comparison with `Form16`

Identical to `Form16` apart from the trailing form number: this walks the gaps adding the scaled
reciprocal at each prime, where `Form16` adds the position reached and encloses through the
offset expansion. Both emit a range theorem of the same shape, both go through the emitter rather
than through generated text, and `Floor` is the import cost of neither.
-/

namespace PrimeCert.GapAB.Form15

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 65536 100003 20 2048 1536 1 15

end PrimeCert.GapAB.Form15
