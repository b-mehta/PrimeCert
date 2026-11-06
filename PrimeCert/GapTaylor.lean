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

/-- The enclosure of one batch from a walk that only adds. `C` and `D` are the walk's own two
literals, the count and the total of the positions it reached; `Vhi`, `Vlo` and `Q` are the
emitter's bounds on the fold of the numbers and the fold of their squares, each tied to `C` and
`D` by a comparison of literals the kernel checks. -/
public theorem primeRecipRange_of_window_walk {w lo len S o A C D Vlo Vhi Q Cw : ℕ}
    (hlo : 1 ≤ lo) (hS : Nat.blt 0 S = true) (ho : Sieve.value lo = o)
    (hbit : ∀ t, lo ≤ t → t < lo + len →
      ((Nat.shiftLeft w lo).testBit t ↔ (Sieve.value t).Prime))
    (hC : sumB (bitAtW w) 0 len 1 = C)
    (hD : sumB (posAtW1 w) 0 len 1 = D)
    (hVhi : Nat.ble (o * C + 3 * D) Vhi = true)
    (hVlo : Nat.ble (Vlo + 4 * C) (o * C + 3 * D) = true)
    (hQb : Nat.ble (o ^ 2 * C + 2 * o * (3 * D) + (3 * len + 1) * (3 * D)) Q = true)
    (hAb : Nat.ble (A * o ^ 2 + Vhi * S) (2 * o * C * S) = true)
    (hUb : Nat.ble (3 * o ^ 2 * C * S + Q * S) ((A + Cw) * o ^ 3 + 3 * o * Vlo * S) = true) :
    PrimeRecipRange (Sieve.value lo) (Sieve.value (lo + len)) A Cw S := by
  rw [Nat.ble_eq] at hVhi hVlo hQb
  subst ho
  have hge : ∀ i < len, Sieve.value lo ≤ Sieve.value (lo + i) := fun i _ ↦
    Sieve.value_strictMono.monotone (Nat.le_add_right lo i)
  have hCs : sumB (bitAtK (Nat.shiftLeft w lo)) lo len 1 = C := by rw [bit_shift, hC]
  have hVs : sumB (valAtK (Nat.shiftLeft w lo)) lo len 1
      = Sieve.value lo * C + sumB (offAtW w lo (Sieve.value lo)) 0 len 1 := by
    rw [val_shift, sumB_valAtW_eq hge, hC]
  have hQs : sumB (sqAtK (Nat.shiftLeft w lo)) lo len 1
      = Sieve.value lo ^ 2 * C + 2 * Sieve.value lo * sumB (offAtW w lo (Sieve.value lo)) 0 len 1
        + sumB (osqAtW w lo (Sieve.value lo)) 0 len 1 := by
    rw [sq_shift, sumB_sqAtW_eq hge, hC]
  have hup := offAtW_le_of_walk (lo := lo) hC hD
  have hdn := le_offAtW_of_walk (lo := lo) hC hD
  have hsq := sumB_osqAtW_le w lo (3 * len + 1) len fun i hi ↦ offAtW_le w lo len i hi
  refine primeRecipRange_of_taylor_bounded hlo hS rfl hbit hCs ?_ ?_ ?_ hAb hUb
  · omega
  · omega
  · have : sumB (osqAtW w lo (Sieve.value lo)) 0 len 1 ≤ (3 * len + 1) * (3 * D) := by
      refine hsq.trans ?_
      exact Nat.mul_le_mul_left _ (by omega)
    have h2 : 2 * Sieve.value lo * sumB (offAtW w lo (Sieve.value lo)) 0 len 1
        ≤ 2 * Sieve.value lo * (3 * D) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- The enclosure of a whole segment from the joined walks. `C` is the count and `D` the total of
the positions counted from the segment's own start, which is what the per-batch walks add up to.
Every other hypothesis is a comparison of literals. -/
public theorem primeRecipRange_of_window_walk0 {w lo len S o A C D E Vlo Vhi Q Cw : ℕ}
    (hlo : 1 ≤ lo) (hS : Nat.blt 0 S = true) (ho : Sieve.value lo = o)
    (hbit : ∀ t, lo ≤ t → t < lo + len →
      ((Nat.shiftLeft w lo).testBit t ↔ (Sieve.value t).Prime))
    (hC : sumB (bitAtW w) 0 len 1 = C)
    (hD : sumB (posAtW0 w lo) 0 len 1 = D)
    (hE : Nat.ble (3 * D + C) (E + 3 * (lo * C)) = true)
    (hVhi : Nat.ble (o * C + 3 * D + C) (Vhi + 3 * (lo * C)) = true)
    (hVlo : Nat.ble (Vlo + C + 3 * (lo * C)) (o * C + 3 * D) = true)
    (hQb : Nat.ble (o ^ 2 * C + 2 * o * E + (3 * len + 1) * E) Q = true)
    (hAb : Nat.ble (A * o ^ 2 + Vhi * S) (2 * o * C * S) = true)
    (hUb : Nat.ble (3 * o ^ 2 * C * S + Q * S) ((A + Cw) * o ^ 3 + 3 * o * Vlo * S) = true) :
    PrimeRecipRange (Sieve.value lo) (Sieve.value (lo + len)) A Cw S := by
  rw [Nat.ble_eq] at hE hVhi hVlo hQb
  subst ho
  have hge : ∀ i < len, Sieve.value lo ≤ Sieve.value (lo + i) := fun i _ ↦
    Sieve.value_strictMono.monotone (Nat.le_add_right lo i)
  have hCs : sumB (bitAtK (Nat.shiftLeft w lo)) lo len 1 = C := by rw [bit_shift, hC]
  have hVs : sumB (valAtK (Nat.shiftLeft w lo)) lo len 1
      = Sieve.value lo * C + sumB (offAtW w lo (Sieve.value lo)) 0 len 1 := by
    rw [val_shift, sumB_valAtW_eq hge, hC]
  have hQs : sumB (sqAtK (Nat.shiftLeft w lo)) lo len 1
      = Sieve.value lo ^ 2 * C + 2 * Sieve.value lo * sumB (offAtW w lo (Sieve.value lo)) 0 len 1
        + sumB (osqAtW w lo (Sieve.value lo)) 0 len 1 := by
    rw [sq_shift, sumB_sqAtW_eq hge, hC]
  have hup := offAtW_le_of_walk0 hC hD
  have hdn := le_offAtW_of_walk0 hC hD
  have hsq := sumB_osqAtW_le w lo (3 * len + 1) len fun i hi ↦ offAtW_le w lo len i hi
  refine primeRecipRange_of_taylor_bounded hlo hS rfl hbit hCs ?_ ?_ ?_ hAb hUb
  · omega
  · omega
  · have hoff : sumB (offAtW w lo (Sieve.value lo)) 0 len 1 ≤ E := by omega
    have h1 : sumB (osqAtW w lo (Sieve.value lo)) 0 len 1 ≤ (3 * len + 1) * E :=
      hsq.trans (Nat.mul_le_mul_left _ hoff)
    have h2 : 2 * Sieve.value lo * sumB (offAtW w lo (Sieve.value lo)) 0 len 1
        ≤ 2 * Sieve.value lo * E := Nat.mul_le_mul_left _ hoff
    omega

/-- One sieved segment enclosed from the joined walks, the counterpart of
`primeRecipRange_segment` for a run in which the kernel never divides. `C` is the count and `D`
the total of the positions counted from the segment's start; the rest are comparisons of
literals. -/
public theorem primeRecipRange_segment_walk {B a W S g o A C D E Vlo Vhi Q Cw : ℕ}
    (ha : a % 6 = 1 ∨ a % 6 = 5) (ha5 : 5 ≤ a) (hBa : B < a)
    (hS : Nat.blt 0 S = true) (ho : Sieve.value (Sieve.index a) = o)
    (htop : Sieve.value (Sieve.index a + W - 1) < B ^ 2)
    (hsound : ∀ j < W, g.testBit j = true →
      ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value (Sieve.index a + j))
    (hcomplete : ∀ j < W,
      (∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value (Sieve.index a + j)) → g.testBit j = true)
    (hC : sumB (bitAtW g) 0 W 1 = C)
    (hD : sumB (posAtW0 g (Sieve.index a)) 0 W 1 = D)
    (hE : Nat.ble (3 * D + C) (E + 3 * (Sieve.index a * C)) = true)
    (hVhi : Nat.ble (o * C + 3 * D + C) (Vhi + 3 * (Sieve.index a * C)) = true)
    (hVlo : Nat.ble (Vlo + C + 3 * (Sieve.index a * C)) (o * C + 3 * D) = true)
    (hQb : Nat.ble (o ^ 2 * C + 2 * o * E + (3 * W + 1) * E) Q = true)
    (hAb : Nat.ble (A * o ^ 2 + Vhi * S) (2 * o * C * S) = true)
    (hUb : Nat.ble (3 * o ^ 2 * C * S + Q * S) ((A + Cw) * o ^ 3 + 3 * o * Vlo * S) = true) :
    PrimeRecipRange a (Sieve.value (Sieve.index a + W)) A Cw S := by
  have hlo : Sieve.value (Sieve.index a) = a := Sieve.value_index ha
  have hmono : ∀ j, Sieve.value (Sieve.index a) ≤ Sieve.value (Sieve.index a + j) := fun j ↦
    Sieve.value_strictMono.monotone (Nat.le_add_right _ _)
  have hlow : ∀ j < W, B < Sieve.value (Sieve.index a + j) := by
    intro j _
    have := hmono j
    omega
  have hhigh : ∀ j < W, Sieve.value (Sieve.index a + j) < B ^ 2 := by
    intro j hj
    have : Sieve.value (Sieve.index a + j) ≤ Sieve.value (Sieve.index a + W - 1) :=
      Sieve.value_strictMono.monotone (by omega)
    omega
  have hiff := segment_bit_iff (fun j hj h ↦ hsound j hj h) hcomplete hlow hhigh
  have hbit : ∀ t, Sieve.index a ≤ t → t < Sieve.index a + W →
      ((Nat.shiftLeft g (Sieve.index a)).testBit t ↔ (Sieve.value t).Prime) := by
    intro t h1 h2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h1
    rw [Nat.shiftLeft_eq', Nat.testBit_shiftLeft]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel_left]
    exact ⟨fun h ↦ (hiff j (by omega)).mp h.2, fun h ↦ ⟨by omega, (hiff j (by omega)).mpr h⟩⟩
  have h1 : 1 ≤ Sieve.index a := by
    rw [Sieve.index]
    omega
  have := primeRecipRange_of_window_walk0 h1 hS ho hbit hC hD hE hVhi hVlo hQb hAb hUb
  rwa [hlo] at this

/-- Everything the segment command's output needs for a run that never divides, in one
application: the base sieve, the run equation, the numeric side conditions as literals, and the
two folds the walks produce. The counterpart of `primeRecipRange_of_segRun`. -/
public theorem primeRecipRange_of_segRun_walk {s B a W S g o A C D E Vlo Vhi Q Cw lo next : ℕ}
    (hs : Sieve.IsSieve B s)
    (ha : Nat.mod a 6 = 1 ∨ Nat.mod a 6 = 5) (hB6 : Nat.mod B 6 = 1 ∨ Nat.mod B 6 = 5)
    (ha5 : Nat.ble 5 a = true) (hW : Nat.blt (W - 1) (2 ^ 32) = true)
    (hB1 : Nat.ble 1 B = true) (h7B : Nat.ble (7 * B) a = true)
    (hS : Nat.blt 0 S = true)
    (hlo : Nat.beq (Sieve.index a) lo = true)
    (htv : Nat.beq (Sieve.value (lo + W)) next = true)
    (hov : Nat.beq (Sieve.value lo) o = true)
    (htop : Nat.blt (Sieve.value (lo + W - 1)) (B ^ 2) = true)
    (hseg : Sieve.segRun s a W B = g)
    (hC : sumB (bitAtW g) 0 W 1 = C)
    (hD : sumB (posAtW0 g lo) 0 W 1 = D)
    (hE : Nat.ble (3 * D + C) (E + 3 * (lo * C)) = true)
    (hVhi : Nat.ble (o * C + 3 * D + C) (Vhi + 3 * (lo * C)) = true)
    (hVlo : Nat.ble (Vlo + C + 3 * (lo * C)) (o * C + 3 * D) = true)
    (hQb : Nat.ble (o ^ 2 * C + 2 * o * E + (3 * W + 1) * E) Q = true)
    (hAb : Nat.ble (A * o ^ 2 + Vhi * S) (2 * o * C * S) = true)
    (hUb : Nat.ble (3 * o ^ 2 * C * S + Q * S) ((A + Cw) * o ^ 3 + 3 * o * Vlo * S) = true) :
    PrimeRecipRange a next A Cw S := by
  rw [Nat.beq_eq] at hlo htv hov
  subst hlo
  subst htv
  rw [Nat.ble_eq] at ha5 hB1 h7B
  rw [Nat.blt_eq] at hW htop
  rw [Sieve.segRun_eq] at hseg
  have hsound' := Sieve.segmentSound_of hs ha hW hB1 h7B
  have hcomplete' := Sieve.segmentComplete_of hs hB6 hW h7B
  rw [Sieve.SegmentSound] at hsound'
  rw [Sieve.SegmentComplete] at hcomplete'
  rw [hseg] at hsound' hcomplete'
  exact primeRecipRange_segment_walk ha ha5 (by omega) hS hov htop
    (fun j hj h ↦ hsound' j hj h) hcomplete' hC hD hE hVhi hVlo hQb hAb hUb

end PrimeCert
