/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Phi

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

/-! # A worked expansion, as a check that the pieces compose

`phiB 10 3` is small enough to reach two independent ways. By the recurrence it splits at 3 and
then at 2, ending at four harmonic leaves; by `phiB_of_lt_sq` it is read off directly, since
`10 < 16` leaves no room for a composite survivor. Both give `47 / 35`, which is also what
`phiSet 10 3 = {1, 5, 7}` says by hand.

This is a test that the derivation API can be applied at all, not a result. The two routes share
no lemma below `phiB` itself, so an error in the recurrence or in the square bound would show up
here as two different values rather than pass quietly.
-/

namespace PrimeCert

open Finset

/-- The value reached by the recurrence, splitting at 3 and then at 2. -/
public theorem phiB_ten_three_of_recurrence : phiB 10 3 = 47 / 35 := by
  have l10 : PhiVal 10 1 _ := .leaf (phiB_one 10)
  have l5 : PhiVal 5 1 _ := .leaf (phiB_one 5)
  have l3 : PhiVal 3 1 _ := .leaf (phiB_one 3)
  have l1 : PhiVal 1 1 _ := .leaf (phiB_one 1)
  have h2a : PhiVal 10 2 _ := PhiVal.split (p := 2) (by norm_num) l10 l5
  have h2b : PhiVal 3 2 _ := PhiVal.split (p := 2) (by norm_num) l3 l1
  have h3 : PhiVal 10 3 _ := PhiVal.split (p := 3) (by norm_num) h2a h2b
  rw [h3.sound]
  norm_num [Finset.sum_filter, Finset.sum_range_succ]

/-- The same value read off the square bound, which applies because `10 < 4 * 4`. -/
public theorem phiB_ten_three_of_lt_sq : phiB 10 3 = 47 / 35 := by
  rw [phiB_of_lt_sq (by norm_num) (by norm_num)]
  norm_num [Finset.sum_filter, Finset.sum_range_succ]

/-- Two windows of a sweep joined into one leaf value, which is the shape a sweep produces: each
window enclosed on its own, the totals and counts added as literals, and the value read at the
end. Stated with the windows as hypotheses, as `Combine.lean` does for the record. -/
public theorem phiB_of_two_ranges {t B b A₁ C₁ A₂ C₂ A C S : ℕ} (ht : 0 < t) (hB : 3 ≤ B)
    (h5b : Nat.ble 5 b = true) (hbt : Nat.ble b (t + 1) = true)
    (h₁ : SievedRecipRange 5 b B A₁ C₁ S) (h₂ : SievedRecipRange b (t + 1) B A₂ C₂ S)
    (hA : Nat.beq (Nat.add A₁ A₂) A = true) (hC : Nat.beq (Nat.add C₁ C₂) C = true) :
    phiB t B ∈ Set.Icc (1 + (A : ℚ) / S) (1 + ((A : ℚ) + (C : ℚ)) / S) :=
  phiB_mem_Icc_of_range ht hB (sievedRecipRange_add h5b hbt h₁ h₂ hA hC)

/-- One branch over two swept leaves, entirely in scaled integer literals: the two leaves come
from the sweep, the two quotients carry the division by `p`, and every side condition is a `Bool`
literal. This is the whole certificate shape for a single split. -/
public theorem phiB_split_of_two_sweeps {t p S A₁ C₁ A₂ C₂ L₁ U₁ L₂ U₂ Qlo Qhi L U : ℕ}
    (hp : p.Prime) (hS : Nat.blt 0 S = true)
    (ht₁ : 0 < t) (ht₂ : 0 < t / p) (hB : 3 ≤ p - 1)
    (hr₁ : SievedRecipRange 5 (t + 1) (p - 1) A₁ C₁ S)
    (hr₂ : SievedRecipRange 5 (t / p + 1) (p - 1) A₂ C₂ S)
    (hL₁ : Nat.beq (S + A₁) L₁ = true) (hU₁ : Nat.beq (S + A₁ + C₁) U₁ = true)
    (hL₂ : Nat.beq (S + A₂) L₂ = true) (hU₂ : Nat.beq (S + A₂ + C₂) U₂ = true)
    (hhi : Nat.ble U₂ (Qhi * p) = true) (hlo : Nat.ble (Qlo * p) L₂ = true)
    (hL : Nat.beq (L + Qhi) L₁ = true) (hU : Nat.beq (U + Qlo) U₁ = true) :
    phiB t p ∈ Set.Icc ((L : ℚ) / S) ((U : ℚ) / S) :=
  phiB_mem_Icc_split hp hS
    (phiB_mem_Icc_of_range_scaled ht₁ hB hS hr₁ hL₁ hU₁)
    (phiB_mem_Icc_of_range_scaled ht₂ hB hS hr₂ hL₂ hU₂)
    hhi hlo hL hU

/-- The two routes to a below-the-square value agree. One counts the survivors directly, the other
expands by least prime factor and finds every branch already finished; this closes only if they
reach the same value, so it is a check on the expansion rather than a restatement. -/
public theorem phiB_routes_agree {t B : ℕ} (ht : 0 < t) (hB : t < (B + 1) * (B + 1)) :
    (1 : ℚ) + ∑ p ∈ (range (t + 1)).filter (fun n ↦ n.Prime ∧ B < n), (p : ℚ)⁻¹
      = 1 + ∑ p ∈ (Finset.Icc (B + 1) t).filter Nat.Prime, (p : ℚ)⁻¹ :=
  (phiB_of_lt_sq ht hB).symm.trans (phiB_eq_one_add_primeSum ht hB)

end PrimeCert
