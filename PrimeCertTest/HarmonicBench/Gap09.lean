/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A whole segment at `10 ^ 9` summed by walking the gaps between its primes

`Ht09_W4` is the same segment, the same divisors and the same enclosure, summed by walking every
position. This one walks only the gaps between consecutive primes, with each batch's rebuilt
window checked against the batch's own window, and the total carried back to the sum over the set
bits by `gapFoldK_div_lit`.
-/

namespace PrimeCert.Gap09

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 1 15

end PrimeCert.Gap09
