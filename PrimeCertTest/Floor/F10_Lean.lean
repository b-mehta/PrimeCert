/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Lean

/-! # The floor with the whole of Lean (see `F0_Bare`)

`Meta.Sieve` costs 296 MB over `SieveCorrect`, of which `Lean.Elab.Command` accounts for 123.
The rest arrives through `PrimeCert.Meta.SieveCache`, whose only import is `public import Lean`.
This file carries that, so the gap against `F9_Elab` says what the whole of Lean costs over the
part of it a command actually needs.
-/

namespace PrimeCert.Floor.F10_Lean

end PrimeCert.Floor.F10_Lean
