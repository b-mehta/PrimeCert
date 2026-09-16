/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Bound `10 ^ 7`, citing the statements written with ordinary numerals

The trailing `0` makes each batch equation cite `sumB_windowEq` and `recip_window`, whose numerals
are the ordinary `0` and `1`, where the emitted statements carry raw literals. `Raw1e7_Raw` is the
same run citing the twins whose numerals match.
-/

namespace PrimeCert.Sieve

run_sieve 10000000

end PrimeCert.Sieve

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_window 10000000 20 2048 0 3 0
