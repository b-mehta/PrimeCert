/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.GapFold

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The enclosure a walk that never divides can reach

`PrimeCert.GapFold` proves that a walk adding the position it reaches yields a count `C` and a
position total `D`, and that those two bound the fold of offsets from `value lo` on both sides.
The three-term expansion wants the fold of the numbers themselves, which such a walk never forms,
so `primeRecipRange_of_taylor_bounded` restates the enclosure with that fold bounded rather than
known: the larger bound answers the lower end of the interval and the smaller bound the upper end.

This lives apart from `GapFold` so that the files a run emits, which import only the walk, do not
carry the field tactics this proof needs.
-/

namespace PrimeCert

private theorem div_le_div_cross {a b c d : ℚ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [div_le_iff₀ hb, div_mul_eq_mul_div, le_div_iff₀ hd]
  exact h

/-- `primeRecipRange_of_taylor` with the fold of the numbers bounded rather than known. -/
public theorem primeRecipRange_of_taylor_bounded {s S lo len o A C Vlo Vhi Q Cw : ℕ}
    (hlo : 1 ≤ lo) (hS : Nat.blt 0 S = true) (ho : Sieve.value lo = o)
    (hbit : ∀ t, lo ≤ t → t < lo + len → (s.testBit t ↔ (Sieve.value t).Prime))
    (hC : sumB (bitAtK s) lo len 1 = C)
    (hVlo : Vlo ≤ sumB (valAtK s) lo len 1)
    (hVhi : sumB (valAtK s) lo len 1 ≤ Vhi)
    (hQ : sumB (sqAtK s) lo len 1 ≤ Q)
    (hAb : Nat.ble (A * o ^ 2 + Vhi * S) (2 * o * C * S) = true)
    (hUb : Nat.ble (3 * o ^ 2 * C * S + Q * S) ((A + Cw) * o ^ 3 + 3 * o * Vlo * S) = true) :
    PrimeRecipRange (Sieve.value lo) (Sieve.value (lo + len)) A Cw S := by
  rw [Nat.blt_eq] at hS
  rw [Nat.ble_eq] at hAb hUb
  subst ho
  have hopos : 0 < Sieve.value lo := by rw [Sieve.value]; omega
  have hv : ∀ n < len, Sieve.value lo ≤ Sieve.value (n * 1 + lo) :=
    fun n _ ↦ Sieve.value_strictMono.monotone (by omega)
  have heq := recipSum_eq_primeSum_range hlo hbit
  have h1 := taylor_le_recipSum (o := Sieve.value lo) s lo len 1 hopos
  have h2 := recipSum_le_taylor (o := Sieve.value lo) s lo len 1 hopos hv
  rw [hC] at h1 h2
  have hoQ : (0 : ℚ) < (Sieve.value lo : ℚ) := by exact_mod_cast hopos
  have hSQ : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS
  have hVhiQ : ((sumB (valAtK s) lo len 1 : ℕ) : ℚ) ≤ (Vhi : ℚ) := by exact_mod_cast hVhi
  have hVloQ : (Vlo : ℚ) ≤ ((sumB (valAtK s) lo len 1 : ℕ) : ℚ) := by exact_mod_cast hVlo
  have hQQ : ((sumB (sqAtK s) lo len 1 : ℕ) : ℚ) ≤ (Q : ℚ) := by exact_mod_cast hQ
  replace h1 : (2 * (Sieve.value lo : ℚ) * C - (Vhi : ℚ)) / (Sieve.value lo : ℚ) ^ 2
      ≤ recipSum s lo len 1 := by
    refine le_trans ?_ h1
    gcongr
  replace h2 : recipSum s lo len 1
      ≤ (3 * (Sieve.value lo : ℚ) ^ 2 * C - 3 * (Sieve.value lo : ℚ) * (Vlo : ℚ) + (Q : ℚ))
          / (Sieve.value lo : ℚ) ^ 3 := by
    refine h2.trans ?_
    gcongr
  have hq1 : (A : ℚ) * (Sieve.value lo : ℚ) ^ 2 + (Vhi : ℚ) * S
      ≤ 2 * (Sieve.value lo : ℚ) * C * S := by exact_mod_cast hAb
  have hq2 : 3 * (Sieve.value lo : ℚ) ^ 2 * C * S + (Q : ℚ) * S
      ≤ ((A : ℚ) + Cw) * (Sieve.value lo : ℚ) ^ 3
        + 3 * (Sieve.value lo : ℚ) * (Vlo : ℚ) * S := by exact_mod_cast hUb
  rw [PrimeRecipRange, ← heq]
  refine ⟨le_trans ?_ h1, h2.trans ?_⟩
  · exact div_le_div_cross hSQ (by positivity) (by nlinarith [hq1])
  · exact div_le_div_cross (by positivity) hSQ (by nlinarith [hq2])

end PrimeCert
