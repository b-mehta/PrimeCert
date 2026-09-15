/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve

/-! # The sieve to `10 ^ 4`, as its own module

The parts of a split run import this, so the sieve is built once and the parts can be built at the
same time.
-/

namespace PrimeCert.Sieve

run_sieve 10000

end PrimeCert.Sieve
