/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
import PrimeCert.Meta.Pocklington3
import PrimeCert.SmallPrimes
import PrimeCert.SieveBase
meta import PrimeCert.Meta.SieveLookup

/-! Interval witnesses, endpoint rejection, and both forms of the `pock3` syntax. -/
open PrimeCert

example : Nat.Prime 73471 := prime_cert%
  [small {2; 31}, pock3 (73471, 3, interval 68, 2 * 31)]
example : Nat.Prime 73471 := prime_cert%
  [small {2; 31}, pock3 (73471, 3, 1, interval 68, 2 * 31)]

-- Neither an endpoint square nor an interval on the wrong side is accepted.
example : (Pocklington3CertMode.interval 3).calculate 5 2 = false := by decide +kernel
example : (Pocklington3CertMode.interval 2).calculate 5 2 = false := by decide +kernel
example : (Pocklington3CertMode.interval 4).calculate 5 1 = true := by decide +kernel
example : (Pocklington3CertMode.interval 5).calculate 5 1 = false := by decide +kernel
example : (Pocklington3CertMode.interval 0).calculate 1 1 = false := by decide +kernel

example : Nat.Prime (2 ^ 255 - 19) := prime_cert%
  [small {2; 223; 353}, sieve {4153; 57467},
   pock3 (31757755568855353, 5, interval 4028944, 2 ^ 3 * 223 * 4153),
   pock3 (74058212732561358302231226437062788676166966415465897661863160754340907,
     2, interval 2028478494862525422475606, 2 * 353 * 57467 * 31757755568855353),
   pock (57896044618658097711785492504343953926634992332820282019728792003956564819949,
     2, 74058212732561358302231226437062788676166966415465897661863160754340907)]
