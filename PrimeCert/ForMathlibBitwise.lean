/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Data.Nat.Bitwise

/-!
# Subtracting a submask

The three facts about `Nat.ldiff` that the sieve uses, in a module whose imports are one file of
Mathlib, so that a file wanting only these pays for only that.
-/

@[simp] public lemma Nat.ldiff_zero_left {b : ℕ} : Nat.ldiff 0 b = 0 :=
  Nat.eq_of_testBit_eq (by simp)

@[simp] public lemma Nat.ldiff_zero_right {b : ℕ} : Nat.ldiff b 0 = b :=
  Nat.eq_of_testBit_eq (by simp)

/-- Disjoint OR equals ADD, for `Nat`; hence subtracting a submask acts as bitwise `ldiff`. -/
public theorem Nat.and_add_ldiff {a b : ℕ} : (a &&& b) + a.ldiff b = a := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp
  | bit ba a' ih =>
    induction b using Nat.binaryRec with
    | zero => simp
    | bit bb b' _ => grind [Nat.land_bit, Nat.ldiff_bit, Nat.bit_val, cases Bool]

public theorem Nat.sub_and_eq_ldiff {a b : ℕ} : a - (a &&& b) = a.ldiff b := by
  grind [Nat.and_add_ldiff]
