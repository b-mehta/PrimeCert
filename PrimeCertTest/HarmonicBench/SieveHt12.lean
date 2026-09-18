/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve

/-! # A sieve to `2 * 10 ^ 6`, for the window at `10 ^ 12`

Sized just above the `1000001` that height crosses off by, so that timing one window there does not
carry the cost of the sieve to `10 ^ 8`.
-/

namespace PrimeCert.Sieve

run_sieve 2000000

end PrimeCert.Sieve
