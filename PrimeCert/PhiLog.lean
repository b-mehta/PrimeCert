/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Phi
public import PrimeCert.LogEnclosure
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith

/-!
# The harmonic leaf, against a logarithm

A branch of the expansion that reaches bound `1` has nothing sieved out, so its value is the
harmonic sum. `PrimeCert/Phi.lean` encloses that by folding the rounded reciprocals, which serves
a small height; the heights the expansion actually reaches run up to `x` itself, where only a
logarithm will do.

Mathlib places the harmonic sum between `γ + log t` and `γ + log (t + 1)`. This file carries that
across to `phiB`, taking the two enclosures as inputs, since a rational enclosure of `log` at a
rational point is the one piece the project does not have.

Kept apart from `PrimeCert/Phi.lean` so that the emitted files, which import that one, pay none of
the analysis this needs.
-/

namespace PrimeCert

open Finset

/-- The value at bound `1` is the harmonic number. -/
public theorem phiB_one_eq_harmonic (t : ℕ) : phiB t 1 = harmonic t := by
  rw [phiB_one, harmonic_eq_sum_Icc]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext n
  simp only [mem_filter, mem_range, Finset.mem_Icc]
  omega

/-- The harmonic leaf from enclosures of the logarithm at `t` and at `t + 1` and of the
Euler-Mascheroni constant. -/
public theorem phiB_one_mem_Icc_of_log {t : ℕ} (ht : 0 < t) {L U G₁ G₂ : ℝ}
    (hL : L ≤ Real.log (t : ℝ)) (hU : Real.log ((t : ℝ) + 1) ≤ U)
    (hG₁ : G₁ ≤ Real.eulerMascheroniConstant) (hG₂ : Real.eulerMascheroniConstant ≤ G₂) :
    ((phiB t 1 : ℚ) : ℝ) ∈ Set.Icc (G₁ + L) (G₂ + U) := by
  rw [phiB_one_eq_harmonic]
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant t
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' t
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq'] at h1 h2
  rw [if_neg (by omega : ¬ t = 0)] at h2
  exact ⟨by linarith, by linarith⟩

/-- The same leaf, with the two logarithms taken from emitted enclosures at a shared scale. -/
public theorem phiB_one_mem_Icc_of_logEnclosure {t lo₁ hi₁ lo₂ hi₂ S : ℕ} (ht : 0 < t)
    (h₁ : LogEnclosure t 1 lo₁ hi₁ S) (h₂ : LogEnclosure (t + 1) 1 lo₂ hi₂ S)
    {G₁ G₂ : ℝ} (hG₁ : G₁ ≤ Real.eulerMascheroniConstant)
    (hG₂ : Real.eulerMascheroniConstant ≤ G₂) :
    ((phiB t 1 : ℚ) : ℝ) ∈ Set.Icc (G₁ + (lo₁ : ℝ) / S) (G₂ + (hi₂ : ℝ) / S) := by
  refine phiB_one_mem_Icc_of_log ht (logEnclosure_nat t lo₁ hi₁ S h₁).1 ?_ hG₁ hG₂
  have := (logEnclosure_nat (t + 1) lo₂ hi₂ S h₂).2
  rwa [Nat.cast_add, Nat.cast_one] at this

end PrimeCert
