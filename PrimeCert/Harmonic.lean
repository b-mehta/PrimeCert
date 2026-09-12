/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib

def myNat (S n : ℕ) : ℕ := n.rec 0 fun i ↦ (S.div i.succ).add
def myRat (S n : ℕ) : ℚ := myNat S n / S

@[simp, grind =] lemma myNat_zero {S : ℕ} : myNat S 0 = 0 := rfl
@[simp, grind =] lemma myNat_succ {S n : ℕ} : myNat S n.succ = S / (n + 1) + myNat S n := rfl

lemma le_harmonic {S n : ℕ} (hS : S ≠ 0) : myRat S n ≤ harmonic n := by
  rw [myRat]
  induction n with
  | zero => simp
  | succ n ih =>
    grw [myNat_succ, Nat.cast_add, Nat.cast_div_le, harmonic_succ, add_div, ih]
    simp [field, add_comm]

lemma harmonic_le {S n : ℕ} (hS : S ≠ 0) : harmonic n ≤ myRat S n + n / S := by
  rw [myRat]
  induction n with
  | zero => simp
  | succ n ih =>
    grw [myNat_succ, harmonic_succ, ih, ← add_div, ← add_div]
    field_simp
    norm_cast
    linear_combination Nat.lt_mul_div_succ S (b := n + 1) (by simp)

lemma le_harmonic_of (S : ℕ) {n : ℕ} {q : ℚ} (hS : S ≠ 0)
    (h : q * S ≤ myNat S n := by decide +kernel) :
    q ≤ harmonic n := by
  grw [← le_harmonic (by simpa), myRat, le_div_iff₀ (by positivity)]; simpa

lemma harmonic_le_of (S : ℕ) {n : ℕ} {q : ℚ} (hS : S ≠ 0)
    (h : myNat S n + n ≤ q * S) : harmonic n ≤ q := by
  grw [harmonic_le (by simpa), myRat, ← add_div, div_le_iff₀ (by positivity)]; simpa

lemma harmonic_mem_Icc (S : ℕ) {n : ℕ} {q₁ q₂ : ℚ}
    (h : q₁ * 10 ^ S ≤ myNat (10 ^ S) n ∧ myNat (10 ^ S) n + n ≤ q₂ * 10 ^ S := by decide +kernel) :
    harmonic n ∈ Set.Icc q₁ q₂ :=
  ⟨le_harmonic_of (10 ^ S) (by simp) (by simp [h]), harmonic_le_of (10 ^ S) (by simp) (by simp [h])⟩

elab "myRfl" : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic (·.assign Lean.reflBoolTrue)

example : harmonic 1000000 ∈ Set.Icc 14.39272672286572358 14.39272672286572369 := harmonic_mem_Icc 24
