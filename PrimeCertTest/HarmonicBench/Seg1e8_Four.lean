/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Four neighbouring windows above `10 ^ 8`, sieved, summed and joined

Each window is 4194304 wheel positions, about 12.6 million consecutive numbers, sieved by the
primes up to `31627`. Together they cover `100000001` to `150331648`, and the join gives one
enclosure over the primes of that whole range at scale `10 ^ 20`. `Seg1e8_W4194304` is the same
work for the first window alone, so the two together say what stacking costs.
-/

namespace PrimeCert.Seg1e8Four

run_segment 100000001 4194304 10542 1536

run_segment 112582913 4194304 10542 1536

run_segment 125165825 4194304 10542 1536

run_segment 137748737 4194304 10542 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 100000001 4194304 31627 20 2048 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 112582913 4194304 31627 20 2048 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 125165825 4194304 31627 20 2048 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 137748737 4194304 31627 20 2048 1536

run_harmonic_join 100000001 4194304 31627 20 4

end PrimeCert.Seg1e8Four
