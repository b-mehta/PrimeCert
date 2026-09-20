/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.SegmentedSieve

/-! # Scratch space for the tree fold's correctness

What the wide band needs: a bit of the flattened tree is a bit of the flattened tree before the
update, or the one bit the update set. Seven levels, each the same shape. -/

namespace PrimeCert.Sieve

open Nat

/-- One level: updating a leaf pair and flattening sets exactly the bit named. Stated on
`k.land 1` rather than on `k < 2`, because `upd2` hands the whole leaf number down and each level
masks its own bit out of it. -/
theorem testBit_flat1_upd1 {t : Lvl1} {k b j : Nat} (hb : b < 65536) :
    (flat1 (upd1 t k b)).testBit j
      = ((flat1 t).testBit j || decide (j = (k.land 1) * 65536 + b)) := by
  have hland : k.land 1 = k % 2 := by
    have h : k.land 1 = k &&& (2 ^ 1 - 1) := rfl
    have h2 : (2 : Nat) ^ 1 = 2 := rfl
    rw [h, Nat.and_two_pow_sub_one_eq_mod, h2]
  have hk : k.land 1 < 2 := by
    rw [hland]
    exact Nat.mod_lt _ (by lia)
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  have hone : ∀ a x : Nat, ((1 : Nat) <<< a).testBit x = decide (x = a) := by
    intro a x
    have hs : (1 : Nat) <<< a = Nat.shiftLeft 1 a := rfl
    rw [hs, testBit_oneShift]
    cases h : Nat.beq x a with
    | true => simp [Nat.eq_of_beq_eq_true h]
    | false => simp [Nat.ne_of_beq_eq_false h]
  unfold upd1 flat1
  cases hbit : Nat.beq (k.land 1) 0 with
  | true =>
    have hz : k.land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, hone]
    rw [hz]
    have hzz : (0 : Nat) * 65536 + b = b := by lia
    rw [hzz]
    cases t.1.testBit j <;> cases decide (j = b) <;>
      cases (decide (j ≥ 65536) && t.2.testBit (j - 65536)) <;> rfl
  | false =>
    have h1 : k.land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, hone]
    rw [h1]
    have hkey : (decide (j ≥ 65536) && decide (j - 65536 = b))
        = decide (j = 1 * 65536 + b) := by
      rcases Nat.lt_or_ge j 65536 with h | h
      · have ha : ¬ (j ≥ 65536) := by lia
        have hbb : ¬ (j = 1 * 65536 + b) := by lia
        simp [ha, hbb]
      · have hbb : (j - 65536 = b) ↔ (j = 1 * 65536 + b) := by
          constructor <;> intro hh <;> lia
        simp [h, hbb]
    rw [← hkey]
    cases t.1.testBit j <;> cases decide (j ≥ 65536) <;>
      cases t.2.testBit (j - 65536) <;> cases decide (j - 65536 = b) <;> rfl

/-- `k.land 1` and `(k.shiftRight 1).land 1` are the low two bits of `k.land 3`. -/
theorem land3_split {k : Nat} :
    k.land 3 = 2 * ((k.shiftRight 1).land 1) + k.land 1 := by
  have h1 : k.land 1 = k % 2 := by
    have h : k.land 1 = k &&& (2 ^ 1 - 1) := rfl
    have h2 : (2 : Nat) ^ 1 = 2 := rfl
    rw [h, Nat.and_two_pow_sub_one_eq_mod, h2]
  have h3 : k.land 3 = k % 4 := by
    have h : k.land 3 = k &&& (2 ^ 2 - 1) := rfl
    have h2 : (2 : Nat) ^ 2 = 4 := rfl
    rw [h, Nat.and_two_pow_sub_one_eq_mod, h2]
  have hsr : k.shiftRight 1 = k / 2 := by
    have h : k.shiftRight 1 = k >>> 1 := rfl
    have hp : (2 : Nat) ^ 1 = 2 := rfl
    rw [h, Nat.shiftRight_eq_div_pow, hp]
  have h2 : (k / 2).land 1 = (k / 2) % 2 := by
    have h : (k / 2).land 1 = (k / 2) &&& (2 ^ 1 - 1) := rfl
    have hh : (2 : Nat) ^ 1 = 2 := rfl
    rw [h, Nat.and_two_pow_sub_one_eq_mod, hh]
  rw [h1, h3, hsr, h2]
  lia

/-- The second level, same shape as the first with the width doubled. -/
theorem testBit_flat2_upd2 {t : Lvl2} {k b j : Nat} (hb : b < 65536) :
    (flat2 (upd2 t k b)).testBit j
      = ((flat2 t).testBit j || decide (j = (k.land 3) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  have hk1 : k.land 1 < 2 := by
    have h : k.land 1 = k % 2 := by
      have hh : k.land 1 = k &&& (2 ^ 1 - 1) := rfl
      have h2 : (2 : Nat) ^ 1 = 2 := rfl
      rw [hh, Nat.and_two_pow_sub_one_eq_mod, h2]
    rw [h]
    exact Nat.mod_lt _ (by lia)
  unfold upd2 flat2
  cases hbit : Nat.beq ((k.shiftRight 1).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 1).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 3 = k.land 1 := by rw [land3_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat1_upd1 hb]
    rw [h3]
    cases (flat1 t.1).testBit j <;> cases decide (j = (k.land 1) * 65536 + b) <;>
      cases (decide (j ≥ 131072) && (flat1 t.2).testBit (j - 131072)) <;> rfl
  | false =>
    have hz : (k.shiftRight 1).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have hlt : (k.shiftRight 1).land 1 < 2 := by
        have h : (k.shiftRight 1).land 1 = (k.shiftRight 1) % 2 := by
          have hh : (k.shiftRight 1).land 1 = (k.shiftRight 1) &&& (2 ^ 1 - 1) := rfl
          have h2 : (2 : Nat) ^ 1 = 2 := rfl
          rw [hh, Nat.and_two_pow_sub_one_eq_mod, h2]
        rw [h]
        exact Nat.mod_lt _ (by lia)
      lia
    have h3 : k.land 3 = 2 + k.land 1 := by rw [land3_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat1_upd1 hb]
    have hkey : (decide (j ≥ 131072) && decide (j - 131072 = (k.land 1) * 65536 + b))
        = decide (j = (k.land 3) * 65536 + b) := by
      rw [h3]
      rcases Nat.lt_or_ge j 131072 with h | h
      · have ha : ¬ (j ≥ 131072) := by lia
        have hbb : ¬ (j = (2 + k.land 1) * 65536 + b) := by lia
        rw [decide_eq_false ha, Bool.false_and, decide_eq_false hbb]
      · have hbb : (j - 131072 = (k.land 1) * 65536 + b)
            ↔ (j = (2 + k.land 1) * 65536 + b) := by
          constructor <;> intro hh <;> lia
        rw [decide_eq_true h, Bool.true_and]
        exact decide_eq_decide.mpr hbb
    rw [← hkey]
    cases (flat1 t.1).testBit j <;> cases decide (j ≥ 131072) <;>
      cases (flat1 t.2).testBit (j - 131072) <;>
      cases decide (j - 131072 = (k.land 1) * 65536 + b) <;> rfl

/-- A mask of `n` ones is a remainder. -/
theorem land_mask_eq {k n : Nat} : k.land (2 ^ n - 1) = k % 2 ^ n := by
  have h : k.land (2 ^ n - 1) = k &&& (2 ^ n - 1) := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

/-- A shift is a division. -/
theorem shiftRightK_eq {k n : Nat} : k.shiftRight n = k / 2 ^ n := by
  have h : k.shiftRight n = k >>> n := rfl
  rw [h, Nat.shiftRight_eq_div_pow]

/-- Bit `n` splits a mask, stated at each width the tree uses. `2 ^ n` as an opaque term makes the
products nonlinear and `lia` cannot close it; with the widths written as literals it can. -/
theorem land_split_lit {k a m : Nat} (ha : a = 2 ^ m) (hb : (2 : Nat) ^ (m + 1) = 2 * a) :
    k % (2 * a) = a * ((k / a) % 2) + k % a := by
  subst ha
  have h1 : 2 ^ m * (k / 2 ^ m) + k % 2 ^ m = k := Nat.div_add_mod k (2 ^ m)
  have h2 : 2 * (k / 2 ^ m / 2) + (k / 2 ^ m) % 2 = k / 2 ^ m := Nat.div_add_mod _ 2
  have h3 : 2 * 2 ^ m * (k / (2 * 2 ^ m)) + k % (2 * 2 ^ m) = k := Nat.div_add_mod k _
  have h4 : k / (2 * 2 ^ m) = k / 2 ^ m / 2 := by
    rw [Nat.mul_comm]
    exact (Nat.div_div_eq_div_mul k (2 ^ m) 2).symm
  rw [h4] at h3
  have hd : 2 ^ m * (k / 2 ^ m)
      = 2 * 2 ^ m * (k / 2 ^ m / 2) + 2 ^ m * ((k / 2 ^ m) % 2) := by
    have e : 2 * 2 ^ m * (k / 2 ^ m / 2) = 2 ^ m * (2 * (k / 2 ^ m / 2)) := by
      rw [Nat.mul_comm 2 (2 ^ m), Nat.mul_assoc]
    rw [e, ← Nat.mul_add, h2]
  -- `lia` reads `2 ^ m * (k / 2 ^ m)` as a product of two unknowns; naming the three products
  -- makes what is left linear in them.
  generalize 2 ^ m * (k / 2 ^ m) = A at h1 hd
  generalize 2 * 2 ^ m * (k / 2 ^ m / 2) = B at h3 hd
  generalize 2 ^ m * ((k / 2 ^ m) % 2) = C at hd ⊢
  lia

/-- The mask split in the `land`/`shiftRight` form the definitions use, at any width. -/
theorem land_split_at {k : Nat} (m a b : Nat) (ha : a = 2 ^ m) (hb : b = 2 * a) :
    k.land (b - 1) = a * ((k.shiftRight m).land 1) + k.land (a - 1) := by
  subst ha
  subst hb
  have hpow : 2 * 2 ^ m = 2 ^ (m + 1) := by
    rw [Nat.pow_succ]
    lia
  have e1 : (k / 2 ^ m).land 1 = (k / 2 ^ m) % 2 := by
    have h : (k / 2 ^ m).land 1 = (k / 2 ^ m).land (2 ^ 1 - 1) := rfl
    have hp : (2 : Nat) ^ 1 = 2 := rfl
    rw [h, land_mask_eq, hp]
  rw [hpow, land_mask_eq, land_mask_eq, shiftRightK_eq, e1, ← hpow]
  exact land_split_lit rfl hpow.symm

/-- One bit is zero or one. -/
theorem land1_lt {k : Nat} : k.land 1 < 2 := by
  have h : k.land 1 = k % 2 := by
    have hh : k.land 1 = k.land (2 ^ 1 - 1) := rfl
    have h2 : (2 : Nat) ^ 1 = 2 := rfl
    rw [hh, land_mask_eq, h2]
  rw [h]
  exact Nat.mod_lt _ (by lia)

/-- A bit at or above a level's width lands in the upper half, and the guarded shift says so. -/
theorem shift_key {j w x : Nat} :
    (decide (j ≥ w) && decide (j - w = x)) = decide (j = w + x) := by
  rcases Nat.lt_or_ge j w with h | h
  · have ha : ¬ (j ≥ w) := by lia
    have hbb : ¬ (j = w + x) := by lia
    rw [decide_eq_false ha, Bool.false_and, decide_eq_false hbb]
  · have hbb : (j - w = x) ↔ (j = w + x) := by
      constructor <;> intro hh <;> lia
    rw [decide_eq_true h, Bool.true_and]
    exact decide_eq_decide.mpr hbb

/-- Bit 2 splits the mask of three ones. -/
theorem land7_split {k : Nat} : k.land 7 = 4 * ((k.shiftRight 2).land 1) + k.land 3 :=
  land_split_at 2 4 8 rfl rfl

/-- Bit 3. -/
theorem land15_split {k : Nat} : k.land 15 = 8 * ((k.shiftRight 3).land 1) + k.land 7 :=
  land_split_at 3 8 16 rfl rfl

/-- Bit 4. -/
theorem land31_split {k : Nat} : k.land 31 = 16 * ((k.shiftRight 4).land 1) + k.land 15 :=
  land_split_at 4 16 32 rfl rfl

/-- Bit 5. -/
theorem land63_split {k : Nat} : k.land 63 = 32 * ((k.shiftRight 5).land 1) + k.land 31 :=
  land_split_at 5 32 64 rfl rfl

/-- Bit 6, the top of a 128-leaf tree. -/
theorem land127_split {k : Nat} : k.land 127 = 64 * ((k.shiftRight 6).land 1) + k.land 63 :=
  land_split_at 6 64 128 rfl rfl

/-- The third level. -/
theorem testBit_flat3_upd3 {t : Lvl3} {k b j : Nat} (hb : b < 65536) :
    (flat3 (upd3 t k b)).testBit j
      = ((flat3 t).testBit j || decide (j = (k.land 7) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd3 flat3
  cases hbit : Nat.beq ((k.shiftRight 2).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 2).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 7 = k.land 3 := by rw [land7_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat2_upd2 hb]
    rw [h3]
    cases (flat2 t.1).testBit j <;> cases decide (j = (k.land 3) * 65536 + b) <;>
      cases (decide (j ≥ 262144) && (flat2 t.2).testBit (j - 262144)) <;> rfl
  | false =>
    have hz : (k.shiftRight 2).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 2)
      lia
    have h3 : k.land 7 = 4 + k.land 3 := by rw [land7_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat2_upd2 hb]
    have hkey : (decide (j ≥ 262144) && decide (j - 262144 = (k.land 3) * 65536 + b))
        = decide (j = (k.land 7) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 262144 + ((k.land 3) * 65536 + b) = (4 + k.land 3) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat2 t.1).testBit j <;> cases decide (j ≥ 262144) <;>
      cases (flat2 t.2).testBit (j - 262144) <;>
      cases decide (j - 262144 = (k.land 3) * 65536 + b) <;> rfl

/-- The fourth level. -/
theorem testBit_flat4_upd4 {t : Lvl4} {k b j : Nat} (hb : b < 65536) :
    (flat4 (upd4 t k b)).testBit j
      = ((flat4 t).testBit j || decide (j = (k.land 15) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd4 flat4
  cases hbit : Nat.beq ((k.shiftRight 3).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 3).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 15 = k.land 7 := by rw [land15_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat3_upd3 hb]
    rw [h3]
    cases (flat3 t.1).testBit j <;> cases decide (j = (k.land 7) * 65536 + b) <;>
      cases (decide (j ≥ 524288) && (flat3 t.2).testBit (j - 524288)) <;> rfl
  | false =>
    have hz : (k.shiftRight 3).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 3)
      lia
    have h3 : k.land 15 = 8 + k.land 7 := by rw [land15_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat3_upd3 hb]
    have hkey : (decide (j ≥ 524288) && decide (j - 524288 = (k.land 7) * 65536 + b))
        = decide (j = (k.land 15) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 524288 + ((k.land 7) * 65536 + b) = (8 + k.land 7) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat3 t.1).testBit j <;> cases decide (j ≥ 524288) <;>
      cases (flat3 t.2).testBit (j - 524288) <;>
      cases decide (j - 524288 = (k.land 7) * 65536 + b) <;> rfl

/-- The fifth level. -/
theorem testBit_flat5_upd5 {t : Lvl5} {k b j : Nat} (hb : b < 65536) :
    (flat5 (upd5 t k b)).testBit j
      = ((flat5 t).testBit j || decide (j = (k.land 31) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd5 flat5
  cases hbit : Nat.beq ((k.shiftRight 4).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 4).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 31 = k.land 15 := by rw [land31_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat4_upd4 hb]
    rw [h3]
    cases (flat4 t.1).testBit j <;> cases decide (j = (k.land 15) * 65536 + b) <;>
      cases (decide (j ≥ 1048576) && (flat4 t.2).testBit (j - 1048576)) <;> rfl
  | false =>
    have hz : (k.shiftRight 4).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 4)
      lia
    have h3 : k.land 31 = 16 + k.land 15 := by rw [land31_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat4_upd4 hb]
    have hkey : (decide (j ≥ 1048576) && decide (j - 1048576 = (k.land 15) * 65536 + b))
        = decide (j = (k.land 31) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 1048576 + ((k.land 15) * 65536 + b) = (16 + k.land 15) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat4 t.1).testBit j <;> cases decide (j ≥ 1048576) <;>
      cases (flat4 t.2).testBit (j - 1048576) <;>
      cases decide (j - 1048576 = (k.land 15) * 65536 + b) <;> rfl

/-- The sixth level, which spans the whole window. -/
theorem testBit_flat6_upd6 {t : Lvl6} {k b j : Nat} (hb : b < 65536) :
    (flat6 (upd6 t k b)).testBit j
      = ((flat6 t).testBit j || decide (j = (k.land 63) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd6 flat6
  cases hbit : Nat.beq ((k.shiftRight 5).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 5).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 63 = k.land 31 := by rw [land63_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat5_upd5 hb]
    rw [h3]
    cases (flat5 t.1).testBit j <;> cases decide (j = (k.land 31) * 65536 + b) <;>
      cases (decide (j ≥ 2097152) && (flat5 t.2).testBit (j - 2097152)) <;> rfl
  | false =>
    have hz : (k.shiftRight 5).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 5)
      lia
    have h3 : k.land 63 = 32 + k.land 31 := by rw [land63_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat5_upd5 hb]
    have hkey : (decide (j ≥ 2097152) && decide (j - 2097152 = (k.land 31) * 65536 + b))
        = decide (j = (k.land 63) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 2097152 + ((k.land 31) * 65536 + b) = (32 + k.land 31) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat5 t.1).testBit j <;> cases decide (j ≥ 2097152) <;>
      cases (flat5 t.2).testBit (j - 2097152) <;>
      cases decide (j - 2097152 = (k.land 31) * 65536 + b) <;> rfl

/-- The seventh level, which the window never reaches but the definitions still carry. -/
theorem testBit_flat7_upd7 {t : Lvl7} {k b j : Nat} (hb : b < 65536) :
    (flat7 (upd7 t k b)).testBit j
      = ((flat7 t).testBit j || decide (j = (k.land 127) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd7 flat7
  cases hbit : Nat.beq ((k.shiftRight 6).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 6).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 127 = k.land 63 := by rw [land127_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat6_upd6 hb]
    rw [h3]
    cases (flat6 t.1).testBit j <;> cases decide (j = (k.land 63) * 65536 + b) <;>
      cases (decide (j ≥ 4194304) && (flat6 t.2).testBit (j - 4194304)) <;> rfl
  | false =>
    have hz : (k.shiftRight 6).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 6)
      lia
    have h3 : k.land 127 = 64 + k.land 63 := by rw [land127_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat6_upd6 hb]
    have hkey : (decide (j ≥ 4194304) && decide (j - 4194304 = (k.land 63) * 65536 + b))
        = decide (j = (k.land 127) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 4194304 + ((k.land 63) * 65536 + b) = (64 + k.land 63) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat6 t.1).testBit j <;> cases decide (j ≥ 4194304) <;>
      cases (flat6 t.2).testBit (j - 4194304) <;>
      cases decide (j - 4194304 = (k.land 63) * 65536 + b) <;> rfl

/-- A failed `blt` is the reverse inequality. -/
theorem blt_false_le {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  by_contra hc
  have h1 : Nat.ble (a + 1) b = true := Nat.ble_eq_true_of_le (by lia)
  have h2 : Nat.blt a b = true := h1
  rw [h2] at h
  exact Bool.noConfusion h

/-- Putting one strike into the tree sets exactly that position, and nothing when the strike falls
past the window's end. -/
theorem testBit_putK {t : Lvl7} {Wm1 s j : Nat} (hW : Wm1 < 4194304) :
    (flat7 (putK t Wm1 s)).testBit j
      = ((flat7 t).testBit j || (decide (s ≤ Wm1) && decide (j = s))) := by
  unfold putK
  cases hblt : Nat.blt Wm1 s with
  | true =>
    have hgt : Wm1 < s := Nat.le_of_ble_eq_true hblt
    have hno : ¬ (s ≤ Wm1) := by lia
    rw [decide_eq_false hno, Bool.false_and, Bool.or_false]
  | false =>
    have hle : s ≤ Wm1 := blt_false_le hblt
    have hb : s.land 65535 < 65536 := by
      have h : s.land 65535 = s % 65536 := by
        have hh : s.land 65535 = s.land (2 ^ 16 - 1) := rfl
        have h2 : (2 : Nat) ^ 16 = 65536 := rfl
        rw [hh, land_mask_eq, h2]
      rw [h]
      exact Nat.mod_lt _ (by lia)
    have hk : (s.shiftRight 16).land 127 = s.shiftRight 16 := by
      have hsr : s.shiftRight 16 = s / 65536 := by
        have h := shiftRightK_eq (k := s) (n := 16)
        have h2 : (2 : Nat) ^ 16 = 65536 := rfl
        rw [h2] at h
        exact h
      have hlt : s / 65536 < 128 := by
        have : s < 4194304 := by lia
        lia
      have hm : (s / 65536).land 127 = (s / 65536) % 128 := by
        have hh : (s / 65536).land 127 = (s / 65536).land (2 ^ 7 - 1) := rfl
        have h2 : (2 : Nat) ^ 7 = 128 := rfl
        rw [hh, land_mask_eq, h2]
      rw [hsr, hm]
      exact Nat.mod_eq_of_lt hlt
    have hpos : (s.shiftRight 16).land 127 * 65536 + s.land 65535 = s := by
      rw [hk]
      have hsr : s.shiftRight 16 = s / 65536 := by
        have h := shiftRightK_eq (k := s) (n := 16)
        have h2 : (2 : Nat) ^ 16 = 65536 := rfl
        rw [h2] at h
        exact h
      have hl : s.land 65535 = s % 65536 := by
        have hh : s.land 65535 = s.land (2 ^ 16 - 1) := rfl
        have h2 : (2 : Nat) ^ 16 = 65536 := rfl
        rw [hh, land_mask_eq, h2]
      rw [hsr, hl]
      have := Nat.div_add_mod s 65536
      lia
    rw [testBit_flat7_upd7 hb, hpos, decide_eq_true hle, Bool.true_and]

/-- The two strikes of one divisor. -/
theorem testBit_treeDiv2K {t : Lvl7} {lo Wm1 p j : Nat} (hW : Wm1 < 4194304) :
    (flat7 (treeDiv2K t lo Wm1 p)).testBit j
      = ((flat7 t).testBit j
          || (decide (firstLocK (indexK (p.mul 5)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 5)) lo (p.mul 2)))
          || (decide (firstLocK (indexK (p.mul 7)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 7)) lo (p.mul 2)))) := by
  unfold treeDiv2K
  rw [testBit_putK hW, testBit_putK hW]

/-- Joining nothing to nothing gives nothing, at any width. -/
theorem lor_shift_zero {w : Nat} : (0 : Nat).lor ((0 : Nat).shiftLeft w) = 0 := by
  have h0 : (0 : Nat).shiftLeft w = 0 <<< w := rfl
  have hl : ∀ n : Nat, (0 : Nat).lor n = n := by
    intro n
    have h : (0 : Nat).lor n = 0 ||| n := rfl
    rw [h, Nat.zero_or]
  rw [hl, h0, Nat.zero_shiftLeft]

/-- An empty tree holds nothing, one level at a time. -/
theorem flat1_zero : flat1 zero1 = 0 := by
  unfold flat1 zero1
  exact lor_shift_zero

/-- Four slices. -/
theorem flat2_zero : flat2 zero2 = 0 := by
  unfold flat2 zero2
  rw [flat1_zero]
  exact lor_shift_zero

/-- Eight. -/
theorem flat3_zero : flat3 zero3 = 0 := by
  unfold flat3 zero3
  rw [flat2_zero]
  exact lor_shift_zero

/-- Sixteen. -/
theorem flat4_zero : flat4 zero4 = 0 := by
  unfold flat4 zero4
  rw [flat3_zero]
  exact lor_shift_zero

/-- Thirty-two. -/
theorem flat5_zero : flat5 zero5 = 0 := by
  unfold flat5 zero5
  rw [flat4_zero]
  exact lor_shift_zero

/-- Sixty-four. -/
theorem flat6_zero : flat6 zero6 = 0 := by
  unfold flat6 zero6
  rw [flat5_zero]
  exact lor_shift_zero

/-- The whole empty tree. -/
theorem flat7_zero : flat7 zero7 = 0 := by
  unfold flat7 zero7
  rw [flat6_zero]
  exact lor_shift_zero

/-- What the tree holds after walking a batch: exactly the in-window strikes of the divisors the
slice names, two to a divisor. The same characterisation `testBit_segAccLoopSK_wide` gives for the
marking side, so the two meet. -/
theorem testBit_treeFold2K {c lo Wm1 start len j : Nat} (hW : Wm1 < 4194304) (hj : j ≤ Wm1) :
    (flat7 (treeFold2K c lo Wm1 start len)).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 2 ∧ testBitK c i = true
        ∧ entrySeedK lo start (8 * i + w) = j := by
  induction len with
  | zero =>
    have hz : treeFold2K c lo Wm1 start 0 = zero7 := rfl
    rw [hz, flat7_zero]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have hadd : start.add len = start + len := rfl
    have hstep : treeFold2K c lo Wm1 start (len + 1)
        = (testBitK c len).rec (treeFold2K c lo Wm1 start len)
            (treeDiv2K (treeFold2K c lo Wm1 start len) lo Wm1 (valueK (start.add len))) := rfl
    rw [hstep]
    cases hb : testBitK c len with
    | false =>
      rw [ih]
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      rw [hadd, testBit_treeDiv2K hW]
      have hA : entrySeedK lo start (8 * len + 0)
          = firstLocK (indexK ((valueK (start + len)).mul 5)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_five
      have hB : entrySeedK lo start (8 * len + 1)
          = firstLocK (indexK ((valueK (start + len)).mul 7)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_seven
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ((h | ⟨-, hjA⟩) | ⟨-, hjB⟩)
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := h
          exact ⟨i, by lia, w, hw, hc, hs⟩
        · exact ⟨len, by lia, 0, by lia, hb, by rw [hA]; exact hjA.symm⟩
        · exact ⟨len, by lia, 1, by lia, hb, by rw [hB]; exact hjB.symm⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact Or.inl (Or.inl ⟨i, h, w, hw, hc, hs⟩)
        · have hil : i = len := by lia
          rw [hil] at hs
          rcases (by lia : w = 0 ∨ w = 1) with hw0 | hw1
          · rw [hw0, hA] at hs
            exact Or.inl (Or.inr ⟨by lia, hs.symm⟩)
          · rw [hw1, hB] at hs
            exact Or.inr ⟨by lia, hs.symm⟩

/-- The tree fold removes from the window exactly what the batch's run removes. No `c < 2 ^ len`
hypothesis: the fold only ever reads positions below `len`, so a bit above it cannot reach the
answer — where the record design needed that bound to stop an entry forging a tally bit. -/
theorem segLoopSCK_eq_tree2 {c lo start len n Wm1 seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 4194304)
    (hwide : ∀ i, i < len → Wm1 < valueK (start + i) * 2) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (treeBatch2K c lo Wm1 start len) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (treeBatch2K c lo Wm1 start len).testBit j = true := by
      rw [testBit_segAccLoopSK_wide hj hwide]
      unfold treeBatch2K
      rw [testBit_treeFold2K hW hj]
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (treeBatch2K c lo Wm1 start len).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

/-- One batch of the widest band, settled by having the kernel place the strikes itself. Five
Boolean hypotheses where `stripeStep` needs eight, because there are no records to bound, no slice
lists to carry and no tally to check. -/
theorem treeStep2 {c lo Wm1 n W start len seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hW4 : Nat.blt Wm1 4194304 = true)
    (hwide : Nat.blt Wm1 (Nat.mul (valueK start) 2) = true)
    (hbatch : Nat.beq (treeBatch2K c lo Wm1 start len) lit = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hW' : Wm1 < 4194304 := Nat.le_of_ble_eq_true hW4
  have hb := Nat.eq_of_beq_eq_true hbatch
  refine Nat.beq_eq.mpr ?_
  rw [segLoopSCK_eq_tree2 hseg hW' (wide_of_blt hwide), hb, ldiff_eq_sub]
  exact Nat.eq_of_beq_eq_true hclear

end PrimeCert.Sieve
