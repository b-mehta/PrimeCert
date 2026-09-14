/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `10 ^ 6`, batches of 5120

The same two reciprocal folds as `N1e6`, over the 333332 mod-6 wheel positions up to `10 ^ 6` at
scale `10 ^ 20`, in batches of 5120 positions, so 66 batches per fold.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic 1000000 20 5120
