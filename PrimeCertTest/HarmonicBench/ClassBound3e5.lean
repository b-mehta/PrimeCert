/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic timing case: bound `3 * 10 ^ 5`, split into 770 position classes

The same enclosure as `Bound3e5`, with each fold split into the 770 residue classes of the
position modulo 770 (the classes of the number modulo 2310), each class cut into batches of 20480
positions.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_classes 300000 20 770 20480
