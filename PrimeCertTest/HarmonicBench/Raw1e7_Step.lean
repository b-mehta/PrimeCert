/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `10 ^ 7`, with the batch fold free of its step and start

The trailing `2` makes each batch sum `sumB1`, which folds `f` over `0 … len - 1` with nothing to
multiply or add per position, where `Raw1e7_Raw` sums `sumB g 0 len 1` and pays a multiplication by
one and an addition of zero at every position. `Raw1e7_Plain` is the same run again with the
statements whose numerals do not match the ones the emitter builds.
-/

namespace PrimeCert.Sieve

run_sieve 10000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 10000000 20 2048 0 3 2
