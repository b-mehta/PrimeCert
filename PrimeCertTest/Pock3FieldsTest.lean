/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

import PrimeCert.Meta.Pocklington3
import PrimeCert.SmallPrimes

/-! # Tests for the `pock3` optional sieve bound

`m` is now optional: the 4-field form `(N, root, mode, F)` computes the sieve bound
automatically; the legacy 5-field form `(N, root, m, mode, F)` still parses and proves.
-/

open PrimeCert

-- new 4-field form: `m` computed automatically
example : Nat.Prime 73471 := prime_cert%
  [small {2; 31}, pock3 (73471, 3, interval, 2 * 31)]

-- legacy 5-field form still parses and proves
example : Nat.Prime 73471 := prime_cert%
  [small {2; 31}, pock3 (73471, 3, 1, interval, 2 * 31)]

-- No auxiliary odd prime is needed, for either syntax form.
example : Nat.Prime 37 := prime_cert% [pock3 (37, 2, <, 2 ^ 2)]
example : Nat.Prime 37 := prime_cert% [pock3 (37, 2, 1, <, 2 ^ 2)]
-- A larger sieve bound admits a smaller factored part.
example : Nat.Prime 197 := prime_cert% [pock3 (197, 2, <, 2 ^ 2)]
example : Nat.Prime 197 := prime_cert% [pock3 (197, 2, 2, <, 2 ^ 2)]
