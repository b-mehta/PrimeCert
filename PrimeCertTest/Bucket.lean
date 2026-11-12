/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.SegmentedSieve

/-! # Scratch: what joining a whole leaf does, one bit at a time

`testBit_flat1_upd1` upward says where a single strike lands. These say the same for `updL1`
upward, which joins a whole leaf at once: the leaf `v` appears at leaf `k`, which is exactly the
single-strike statement with `v = 1 <<< b`.

This is the groundwork the bucketed dispatch needs. The widest band is 39% of a window's kernel,
of which about 43 s is the per-strike descent through the tree; mode 61 measured that joining a
leaf instead costs under the noise floor. -/

namespace PrimeCert.Sieve

/-- A local copy of the module's `land1_lt`, which is file-local there. Drop this when the text
below moves into `SegmentedSieve.lean`. -/
theorem land1_lt' {k : Nat} : k.land 1 < 2 := by
  have h : k.land 1 = k % 2 := by
    have hl : k.land 1 = k &&& (2 ^ 1 - 1) := rfl
    rw [hl, Nat.and_two_pow_sub_one_eq_mod]
  rw [h]
  omega

/-- Joining a leaf at the bottom level. -/
theorem testBit_flat1_updL1 {t : Lvl1} {k v j : Nat} :
    (flat1 (updL1 t k v)).testBit j
      = ((flat1 t).testBit j || (v <<< ((k.land 1) * 65536)).testBit j) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold updL1 flat1
  cases hbit : Nat.beq (k.land 1) 0 with
  | true =>
    have hz : k.land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft]
    rw [hz]
    simp only [Nat.zero_mul, Nat.sub_zero, Nat.zero_le, decide_true, Bool.true_and]
    cases t.1.testBit j <;> cases v.testBit j <;>
      cases (decide (j ≥ 65536) && t.2.testBit (j - 65536)) <;> rfl
  | false =>
    have h1 : k.land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt' (k := k)
      lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft]
    rw [h1]
    simp only [Nat.one_mul]
    cases t.1.testBit j <;> cases decide (65536 ≤ j) <;> cases t.2.testBit (j - 65536) <;>
      cases v.testBit (j - 65536) <;> rfl

end PrimeCert.Sieve
