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

end PrimeCert.Sieve
