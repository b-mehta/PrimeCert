import PrimeCert.Meta.Pocklington3
import PrimeCert.SmallPrimes

/-! # Tests for the `pock3` field simplification (Task 4)

`m` is now optional: the 4-field form `(N, root, mode, F)` computes the sieve bound
automatically; the legacy 5-field form `(N, root, m, mode, F)` still parses but is deprecated.
-/

open PrimeCert

-- new 4-field form: `m` computed automatically
theorem pock3_no_m : Nat.Prime 73471 := prime_cert%
  [small {2; 7; 31}, pock3 (73471, 3, 7, 2 * 31)]

-- legacy 5-field form still parses and proves, but emits a deprecation warning
/-- warning: the `m` argument to `pock3` is deprecated and now computed automatically; use `pock3 (N, root, mode, F)` -/
#guard_msgs in
theorem pock3_legacy_m : Nat.Prime 73471 := prime_cert%
  [small {2; 7; 31}, pock3 (73471, 3, 1, 7, 2 * 31)]
