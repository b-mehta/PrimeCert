/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `3 * 10 ^ 5`, batches of 20480 -/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic 300000 20 20480
