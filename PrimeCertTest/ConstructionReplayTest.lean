/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
import PrimeCert
import PrimeCert.SieveBase
meta import PrimeCert.Meta.SieveLookup

/-! The suggested certificate builds with no import of certificate construction. -/
example : Nat.Prime (2 ^ 255 - 19) := by
  exact prime_cert%
    [sieve {2; 223; 4153; 57467; 132049},
     pock3 (31757755568855353, 5, 1, interval 4028944, 2 ^ 3 * 223 * 4153),
     pock3 (74058212732561358302231226437062788676166966415465897661863160754340907,
       2, 1, interval 786343672787837091059418602, 2 * 57467 * 132049 * 31757755568855353),
     pock (57896044618658097711785492504343953926634992332820282019728792003956564819949,
       2, 74058212732561358302231226437062788676166966415465897661863160754340907)]
