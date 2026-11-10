/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.BinarySplit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import Mathlib.Tactic.Linarith

/-!
# A logarithm between two scaled integers

`LogEnclosure n d lo hi S` says `log (n/d)` lies between `lo/S` and `hi/S`. It is the same shape
the rest of the project states its enclosures in: two natural numbers over a shared scale, with
every side condition a comparison of numerals.

The value comes from the series `artanh x = ∑ x^(2i+1)/(2i+1)`, which gives
`log ((v+u)/(v-u)) = 2 artanh (u/v)`, summed by `PrimeCert/BinarySplit.lean` and cut off with
Mathlib's bound on the remainder. The series is only short where `u/v` is small, so an argument of
any size is first divided by a power of two (`logEnclosure_shift`), leaving `log 2` to be enclosed
once by the same means.

The harmonic leaf of `PrimeCert/PhiLog.lean` is the consumer: it wants `log t` and `log (t+1)` at
a height the fold cannot reach.
-/

namespace PrimeCert

open Finset

/-- The numerator of the ratio between consecutive `artanh` terms: `u² (2k+1)`. Written in the
primitive operations, so that an emitted side condition meets the kernel without unfolding
notation. -/
@[expose] public def artanhP (u : ℕ) : ℕ → ℕ :=
  fun k ↦ Nat.mul (Nat.pow u 2) (Nat.succ (Nat.mul 2 k))

/-- The denominator of that ratio: `v² (2k+3)`. -/
@[expose] public def artanhQ (v : ℕ) : ℕ → ℕ :=
  fun k ↦ Nat.mul (Nat.pow v 2) (Nat.add (Nat.mul 2 k) 3)

/-- `log (n/d)` lies between `lo/S` and `hi/S`. -/
public def LogEnclosure (n d lo hi S : ℕ) : Prop :=
  Real.log ((n : ℝ) / (d : ℝ)) ∈ Set.Icc ((lo : ℝ) / S) ((hi : ℝ) / S)

private theorem prod_2k3 (i : ℕ) :
    ∏ k ∈ range i, (2 * k + 3) = (∏ k ∈ range i, (2 * k + 1)) * (2 * i + 1) := by
  induction i with
  | zero => simp
  | succ n ih => rw [prod_range_succ, ih, prod_range_succ]; ring

/-- One running product of the split is an `artanh` term shifted by one. -/
private theorem artanh_fold_term (u v i : ℕ) (hv : v ≠ 0) :
    ∏ j ∈ Finset.Ico 0 (i + 1), ((artanhP u j : ℚ) / (artanhQ v j))
      = ((u : ℚ) / v) ^ (2 * (i + 1)) / ((2 * (i + 1) + 1 : ℕ) : ℚ) := by
  rw [← Finset.range_eq_Ico]
  simp only [artanhP, artanhQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.succ_eq_add_one]
  rw [Finset.prod_div_distrib]
  have hnum : (∏ k ∈ Finset.range (i + 1), ((u ^ 2 * (2 * k + 1) : ℕ) : ℚ))
      = (u : ℚ) ^ (2 * (i + 1)) * ∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hden : (∏ k ∈ Finset.range (i + 1), ((v ^ 2 * (2 * k + 3) : ℕ) : ℚ))
      = (v : ℚ) ^ (2 * (i + 1)) *
        ((∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ)) * (2 * (i + 1) + 1)) := by
    push_cast
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    congr 1
    exact_mod_cast prod_2k3 (i + 1)
  rw [hnum, hden, div_pow]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hp1 : (∏ k ∈ Finset.range (i + 1), ((2 * k + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp

/-- What the split computes for `artanh`: with `(T, Q, P)` the split over `0` to `N - 1`, the
partial sum `∑_{i < N} (u/v)^(2i+1)/(2i+1)` is `u (Q + T) / (v Q)`. -/
private theorem artanh_value (u v N T Q P : ℕ) (hv : v ≠ 0) (hN : 1 ≤ N)
    (h : (T, Q, P) = binarySplit (artanhP u) (artanhQ v) 0 (N - 1)) :
    ((u : ℚ) * (Q + T) / (v * Q))
      = ∑ i ∈ Finset.range N, ((u : ℚ) / v) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ) := by
  have hqne : ∀ i, artanhQ v i ≠ 0 := by
    intro i
    simp only [artanhQ, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
    exact Nat.mul_ne_zero (pow_ne_zero 2 hv) (by omega)
  have hQ0 : Q ≠ 0 := by
    have hb := binarySplit_nonzero (p := artanhP u) (q := artanhQ v) (m := 0) (n := N - 1) hqne
    rw [← h] at hb
    simpa using hb
  have hspec := (binarySplit_spec (p := artanhP u) (q := artanhQ v)
    (m := 0) (n := N - 1) hqne h).2
  rw [Finset.sum_congr rfl (fun i _ ↦ artanh_fold_term u v i hv)] at hspec
  rw [← Finset.range_eq_Ico] at hspec
  have hNeq : N = N - 1 + 1 := by omega
  rw [hNeq, Finset.sum_range_succ']
  have hterm : ∀ i ∈ Finset.range (N - 1),
      ((u : ℚ) / v) ^ (2 * (i + 1) + 1) / ((2 * (i + 1) + 1 : ℕ) : ℚ)
        = ((u : ℚ) / v) * (((u : ℚ) / v) ^ (2 * (i + 1)) / ((2 * (i + 1) + 1 : ℕ) : ℚ)) := by
    intro i _
    rw [pow_succ']
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hspec]
  have hv' : (v : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hv
  have hQ0' : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hQ0
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.cast_one, div_one]
  field_simp
  ring

/-- Where `2u² ≤ v²` the geometric factor the remainder carries is at most `2`. -/
private theorem geo_factor_le (x D : ℝ) (hD : 0 < D) (hx : 2 * x ^ 2 ≤ D ^ 2) :
    (1 - (x / D) ^ 2)⁻¹ ≤ 2 := by
  have h2 : (x / D) ^ 2 ≤ 1 / 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  rw [← one_div]
  calc 1 / (1 - (x / D) ^ 2) ≤ 1 / (1 / 2) :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
    _ = 2 := by norm_num

/-- The enclosure the series gives. The argument is `(v+u)/(v-u)`, the sum runs to `N` terms, and
the three comparisons say in turn that the remainder is under `1/S`, that `lo/S` is under twice
the partial sum, and that twice the partial sum is under `hi/S`, each with a unit of the scale to
spare. -/
public theorem logEnclosure_of_split (u v N Nm T Q P n d lo hi S : ℕ)
    (huv : u.blt v) (hg : (Nat.mul 2 (u.pow 2)).ble (v.pow 2))
    (hQ : Nat.ble 1 Q) (hS : Nat.ble 1 S) (hv : Nat.ble 1 v)
    (hN : N.beq (Nm.succ)) (hn : n.beq (v.add u)) (hd : d.beq (v.sub u))
    (hsplit : binarySplit (artanhP u) (artanhQ v) 0 Nm = (T, Q, P))
    (htail : ((Nat.mul 4 (u.pow ((Nat.mul 2 N).succ))).mul S).ble (v.pow ((Nat.mul 2 N).succ)))
    (hlo : ((lo.add 1).mul (v.mul Q)).ble ((Nat.mul 2 (u.mul (Q.add T))).mul S))
    (hhi : (((Nat.mul 2 (u.mul (Q.add T))).mul S).add (v.mul Q)).ble (hi.mul (v.mul Q))) :
    LogEnclosure n d lo hi S := by
  obtain rfl : N = Nm + 1 := Nat.eq_of_beq_eq_true hN
  obtain rfl : n = v + u := Nat.eq_of_beq_eq_true hn
  obtain rfl : d = v - u := Nat.eq_of_beq_eq_true hd
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq,
    Nat.succ_eq_add_one] at huv hg hQ hS hv htail hlo hhi
  have hvne : v ≠ 0 := by omega
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hS0 : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  have hden0 : (0 : ℝ) < (v : ℝ) * Q := mul_pos hv0 hQ0
  -- the split's value, as a real, is the partial sum
  have hsumR : (u : ℝ) * ((Q : ℝ) + T) / ((v : ℝ) * Q)
      = ∑ i ∈ Finset.range (Nm + 1), ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    have hq := artanh_value u v (Nm + 1) T Q P hvne (by omega) (by simpa using hsplit.symm)
    have hr := congrArg (fun r : ℚ ↦ (r : ℝ)) hq
    push_cast at hr
    rw [hr]
  -- twice the partial sum is within `1/S` of the logarithm
  have hx : |(u : ℝ) / v| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one hv0]
    exact_mod_cast huv
  have hm := Real.sum_range_sub_log_div_le hx (Nm + 1)
  have harg : ((1 : ℝ) + (u : ℝ) / v) / (1 - (u : ℝ) / v)
      = ((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ) := by
    rw [Nat.cast_sub huv.le]
    push_cast
    field_simp
  rw [harg] at hm
  have hA2 : (4 : ℝ) * ((u : ℝ) / v) ^ (2 * (Nm + 1) + 1) ≤ 1 / S := by
    rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hS0, one_mul]
    exact_mod_cast htail
  have hclose : |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ))
      - 2 * ((u : ℝ) * ((Q : ℝ) + T) / ((v : ℝ) * Q))| ≤ 1 / S := by
    rw [hsumR]
    have habs : |Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ)) -
          2 * ∑ i ∈ Finset.range (Nm + 1), ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)|
        = 2 * |1 / 2 * Real.log (((v + u : ℕ) : ℝ) / ((v - u : ℕ) : ℝ)) -
          ∑ i ∈ Finset.range (Nm + 1), ((u : ℝ) / v) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)| := by
      rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul]
      congr 1
      ring
    rw [habs]
    refine (mul_le_mul_of_nonneg_left hm (by norm_num)).trans ?_
    have hdm : ((u : ℝ) / v) ^ (2 * (Nm + 1) + 1) / (1 - ((u : ℝ) / v) ^ 2)
        = ((u : ℝ) / v) ^ (2 * (Nm + 1) + 1) * (1 - ((u : ℝ) / v) ^ 2)⁻¹ := div_eq_mul_inv _ _
    rw [abs_of_nonneg (by positivity), hdm]
    have hgf := geo_factor_le u v hv0 (by exact_mod_cast hg)
    calc 2 * (((u : ℝ) / v) ^ (2 * (Nm + 1) + 1) * (1 - ((u : ℝ) / v) ^ 2)⁻¹)
        ≤ 2 * (((u : ℝ) / v) ^ (2 * (Nm + 1) + 1) * 2) := by gcongr
      _ = 4 * ((u : ℝ) / v) ^ (2 * (Nm + 1) + 1) := by ring
      _ ≤ 1 / S := hA2
  -- and the two comparisons place that value between the ends
  have hval : 2 * ((u : ℝ) * ((Q : ℝ) + T) / ((v : ℝ) * Q))
      = ((2 * (u * (Q + T)) : ℕ) : ℝ) / ((v * Q : ℕ) : ℝ) := by push_cast; ring
  have hlo' : ((lo : ℝ) + 1) / S ≤ 2 * ((u : ℝ) * ((Q : ℝ) + T) / ((v : ℝ) * Q)) := by
    rw [hval, div_le_div_iff₀ hS0 (by exact_mod_cast hden0)]
    have : (((lo + 1) * (v * Q) : ℕ) : ℝ) ≤ ((2 * (u * (Q + T)) * S : ℕ) : ℝ) := by
      exact_mod_cast hlo
    push_cast at this ⊢
    linarith
  have hhi' : 2 * ((u : ℝ) * ((Q : ℝ) + T) / ((v : ℝ) * Q)) ≤ ((hi : ℝ) - 1) / S := by
    rw [hval, div_le_div_iff₀ (by exact_mod_cast hden0) hS0]
    have : ((2 * (u * (Q + T)) * S + v * Q : ℕ) : ℝ) ≤ ((hi * (v * Q) : ℕ) : ℝ) := by
      exact_mod_cast hhi
    push_cast at this ⊢
    linarith
  have hb := abs_le.mp hclose
  have hdlo : ((lo : ℝ) + 1) / S - 1 / S = (lo : ℝ) / S := by ring
  have hdhi : ((hi : ℝ) - 1) / S + 1 / S = (hi : ℝ) / S := by ring
  exact ⟨by linarith [hb.1, hlo'], by linarith [hb.2, hhi']⟩

/-- An argument of `1`, where the series has nothing to say and the value is exactly zero. -/
public theorem logEnclosure_one (n S : ℕ) : LogEnclosure n n 0 0 S := by
  simp only [LogEnclosure, Set.mem_Icc, Nat.cast_zero, zero_div]
  rcases eq_or_ne (n : ℝ) 0 with h | h
  · simp [h]
  · rw [div_self h, Real.log_one]
    exact ⟨le_rfl, le_rfl⟩

/-- The same enclosure for any other way of writing the argument. -/
public theorem logEnclosure_of_eq (A B n d lo hi S : ℕ) (hB : Nat.ble 1 B) (hd : Nat.ble 1 d)
    (he : (A.mul d).beq (n.mul B)) (h : LogEnclosure A B lo hi S) :
    LogEnclosure n d lo hi S := by
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.mul_eq] at hB hd he
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hAB : (A : ℝ) / B = (n : ℝ) / d := by
    rw [div_eq_div_iff hB0.ne' hd0.ne']
    exact_mod_cast he
  simp only [LogEnclosure] at h ⊢
  rwa [hAB] at h

/-- Division of the argument by a power of two, paid for with that many copies of `log 2`. This is
what lets the series be short: `n / (d · 2^k)` is taken near `1`, where few terms suffice. -/
public theorem logEnclosure_shift (n d k lo hi l₂ h₂ lo' hi' S : ℕ)
    (hn : Nat.ble 1 n) (hd : Nat.ble 1 d)
    (hr : LogEnclosure n (d.mul (Nat.pow 2 k)) lo hi S)
    (htwo : LogEnclosure 2 1 l₂ h₂ S)
    (hlo : lo'.beq (lo.add (k.mul l₂))) (hhi : hi'.beq (hi.add (k.mul h₂))) :
    LogEnclosure n d lo' hi' S := by
  simp only [Nat.ble_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hn hd hlo hhi
  obtain rfl : lo' = lo + k * l₂ := hlo
  obtain rfl : hi' = hi + k * h₂ := hhi
  simp only [LogEnclosure, Nat.mul_eq, Nat.pow_eq, Set.mem_Icc] at hr htwo ⊢
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have htwo' : (2 : ℝ) = ((2 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
  rw [← htwo'] at htwo
  have hsplit : Real.log ((n : ℝ) / d)
      = Real.log ((n : ℝ) / ((d * 2 ^ k : ℕ) : ℝ)) + (k : ℝ) * Real.log 2 := by
    have hc : ((d * 2 ^ k : ℕ) : ℝ) = (d : ℝ) * 2 ^ k := by push_cast; ring
    rw [hc, ← div_div, Real.log_div (div_ne_zero hn0.ne' hd0.ne') (pow_ne_zero k two_ne_zero),
      Real.log_pow]
    ring
  rw [hsplit]
  constructor
  · have h1 : (k : ℝ) * ((l₂ : ℝ) / S) ≤ (k : ℝ) * Real.log 2 := by
      have := htwo.1
      have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left this hk
    have : ((lo + k * l₂ : ℕ) : ℝ) / S = (lo : ℝ) / S + (k : ℝ) * ((l₂ : ℝ) / S) := by
      push_cast
      ring
    rw [this]
    exact add_le_add hr.1 h1
  · have h1 : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * ((h₂ : ℝ) / S) := by
      have := htwo.2
      have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left this hk
    have : ((hi + k * h₂ : ℕ) : ℝ) / S = (hi : ℝ) / S + (k : ℝ) * ((h₂ : ℝ) / S) := by
      push_cast
      ring
    rw [this]
    exact add_le_add hr.2 h1

/-- The logarithm of a whole number, the form the harmonic leaf asks for. -/
public theorem logEnclosure_nat (n lo hi S : ℕ) (h : LogEnclosure n 1 lo hi S) :
    Real.log (n : ℝ) ∈ Set.Icc ((lo : ℝ) / S) ((hi : ℝ) / S) := by
  simpa [LogEnclosure] using h

end PrimeCert
