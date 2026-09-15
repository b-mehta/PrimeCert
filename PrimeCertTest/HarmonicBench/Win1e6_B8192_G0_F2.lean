/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Window A/B case: bound `10 ^ 6`, windows of 8192 positions, one chain, two folds -/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 1000000 20 8192 0 2
