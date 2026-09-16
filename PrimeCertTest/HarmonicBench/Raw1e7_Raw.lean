/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `10 ^ 7`, citing the statements whose numerals are raw literals

The trailing `1` makes each batch equation cite `sumB_windowEqR` and `recip_windowR`, whose
numerals are written the way the emitter builds them. `Raw1e7_Plain` is the same run citing the
ordinary forms.
-/

namespace PrimeCert.Sieve

run_sieve 10000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 10000000 20 2048 0 3 1
