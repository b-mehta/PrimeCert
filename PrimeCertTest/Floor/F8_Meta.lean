/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve

/-! # The floor with the sieve command alone (see `F0_Bare`)

`SieveBase` adds 292 MB over `SieveCorrect`, and I guessed that the chained proofs `run_sieve`
emits hold it. The sieve session read their own file and refuted that: `run_sieve 1000000` sieves
only to the square root, so it emits 21 batch lemmas carrying under a megabyte between them.
What `SieveBase` does introduce, first in the chain, is `PrimeCert.Meta.Sieve`, which imports
`Lean.Elab.Command`. This file carries that and nothing else, and `F9_Elab` carries the
elaborator alone, so the pair says how much of the 292 belongs to each.
-/

namespace PrimeCert.Floor.F8_Meta

end PrimeCert.Floor.F8_Meta
