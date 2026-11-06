/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.QuickRfl
public import PrimeCert.PrimeHarmonic

/-! # 2 folds of 20000 running-sum updates

The identity carries one running sum for each of the 1 primes below its cut, and
sweeping a segment updates them as multiples are cleared. With no mutable store the sums
sit side by side in one literal of 60 bits, so an update adds into a field
of a wide number and costs what that width costs, not what the addend costs.

Nothing here is proved to be an update of anything; the file is for timing.
-/

set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace PrimeCert.UpdateProbe.U1_20000

open PrimeCert

/-- One sweep of updates over the packed sums, in the operations the kernel reads. -/
@[expose] public noncomputable def updateFold (W0 F M c : ℕ) : ℕ :=
  c.rec W0 fun i st ↦
    Nat.add st (Nat.shiftLeft (nat_lit 1) (Nat.mul F (Nat.mod i M)))

/-- 20000 updates into 1 fields of 60 bits. -/
public theorem sweep_0 : Nat.beq (updateFold 6 60 1 20000) 20006 = true := by
  quickRfl

/-- 20000 updates into 1 fields of 60 bits. -/
public theorem sweep_1 : Nat.beq (updateFold 7 60 1 20000) 20007 = true := by
  quickRfl

end PrimeCert.UpdateProbe.U1_20000
