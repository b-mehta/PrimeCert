/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A segment at `10 ^ 9` crossed off by the sorted-strike routine

`Ht09_F7W2` is the same segment, the same divisors and the same sum, crossed off by the clamped
loop reading slices. This one uses the routine that sorts the strikes of a divisor whose multiples
land once or twice into the 65536 bit pieces they fall in.
-/

namespace PrimeCert.Ht09_M28

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 524288 100003 20 2048 1536 1 7 28

end PrimeCert.Ht09_M28
