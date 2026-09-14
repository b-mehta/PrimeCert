/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic

/-! # Harmonic benchmark baseline: startup

Measures what every other case in this directory pays before doing any work of its own: process
startup, the import closure of `PrimeCert.Meta.PrimeHarmonic`, and the `run_sieve 1000000` that
`PrimeCert.SieveBase` performs on import. Carries no kernel reduction of its own. Subtract this
from every other case in the directory.
-/
