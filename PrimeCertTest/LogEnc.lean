/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.LogEnclosure

/-! # Logarithms at twenty places

`run_log` emitting the constant the harmonic leaf waits on, and a few arguments of the size that
leaf meets. Each is stated at scale `10 ^ 20`, and `log 2` is emitted once and reused.
-/

namespace PrimeCert.LogEncTest

run_log 2 1 20

run_log 3 1 20

run_log 1000 1 20

run_log 1000 999 20

/-! A height of the size the expansion's harmonic leaves actually reach, and its successor, which
is the other end of the bound Mathlib places the harmonic sum between. -/

run_log 1000000000000 1 25

run_log 1000000000001 1 25

end PrimeCert.LogEncTest
