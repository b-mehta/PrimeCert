/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `10 ^ 6`

Measures the two reciprocal folds over the 333332 mod-6 wheel positions up to `10 ^ 6`, at scale
`10 ^ 20`, in batches of 20480 positions, so 17 batches per fold. That is every position of the
cached sieve. `sieveBits_1000000` is already in the import closure, so this file's cost over
`Base0_Startup` is the folds and nothing else.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic 1000000 20 20480
