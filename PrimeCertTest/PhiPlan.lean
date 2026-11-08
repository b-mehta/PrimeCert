/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PhiPlan

/-! # The leaf counts the emitter would have to produce

Three sizes, against `scripts/count_leaves.py`, which walks the same tree in Python. The counts
agreeing is the check that the emitter's walk is the one the costing was taken from.
-/

namespace PrimeCert.PhiPlanTest

run_phi_plan 1000000000

run_phi_plan 100000000000

end PrimeCert.PhiPlanTest
