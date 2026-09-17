/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.SieveCorrect
public import PrimeCert.SieveBase
public import PrimeCert.SegmentedSieve

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Interval.Set.Defs

import PrimeCert.ForLean
import PrimeCert.ForMathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# A kernel-checked enclosure of the sum of reciprocals of primes

`sumB f start len step` folds `Nat.add` over the `len`-term arithmetic progression
`start, start + step, …`, the additive counterpart of `PrimeCert.forallB`. Reading the sieve bit
first, `recipAtK s S t` contributes the truncated quotient `S / value t` where the bit at `t` is
set and `0` where it is clear, and `bitAtK s t` counts the positions that contribute.

The truncation loses less than `1` per contributing position, so
`recipSum_mem_Icc` sandwiches the exact rational sum between `sumB (recipAtK s S) …  / S` and
`(sumB (recipAtK s S) … + sumB (bitAtK s) …) / S`. `recipSum_eq_primeSum` identifies that exact
sum with `∑ p ∈ (Finset.Icc 5 N).filter Nat.Prime, (p : ℚ)⁻¹` whenever the bitset satisfies
`PrimeCert.Sieve.IsSieve N`.

`sumB_seed`, `sumB_chain` and `sumB_last` stage one long fold across a declaration per batch, and
`primeRecipIcc_of` turns a pair of staged folds into `PrimeRecipIcc`. The command that splices
them is `run_harmonic`, in `PrimeCert.Meta.PrimeHarmonic`; this file carries no kernel reduction
of its own.
-/

namespace PrimeCert

open Finset

/-! ## The kernel-reducible accumulator -/

/-- The sum of `f` over the `len` elements `start, start + step, …`. The additive counterpart of
`forallB`; `sumB_eq_sum` states it as an ordinary `Finset` sum. -/
@[expose] public def sumB (f : ℕ → ℕ) (start len step : ℕ) : ℕ :=
  len.rec 0 fun n b ↦ (f ((n.mul step).add start)).add b

@[simp, grind =] public theorem sumB_zero (f : ℕ → ℕ) (start step : ℕ) :
    sumB f start 0 step = 0 :=
  rfl

@[simp, grind =] theorem sumB_succ (f : ℕ → ℕ) (start len step : ℕ) :
    sumB f start (len + 1) step = f ((len.mul step).add start) + sumB f start len step :=
  rfl

/-- Read the fold as a `Finset` sum over the indices `0` to `len`. -/
public theorem sumB_eq_sum (f : ℕ → ℕ) (start len step : ℕ) :
    sumB f start len step = ∑ n ∈ range len, f (n * step + start) := by
  induction len with
  | zero => rfl
  | succ n ih =>
    rw [sumB_succ, ih, Finset.sum_range_succ]
    exact Nat.add_comm _ _

/-- Fuel additivity: a run of `a + b` steps is a run of `a` followed by a run of `b` from where
the first stopped. This is the glue that stages one long fold across several declarations. -/
public theorem sumB_add (f : ℕ → ℕ) (start a b step : ℕ) :
    sumB f start (a + b) step = sumB f start a step + sumB f (a * step + start) b step := by
  rw [sumB_eq_sum, sumB_eq_sum, sumB_eq_sum, Finset.sum_range_add]
  congr 1
  exact Finset.sum_congr rfl fun n _ ↦ by ring_nf

/-- Splitting a unit-step run into residue classes of the position: the run of `C * L` consecutive
positions from `start` is the sum of the `C` runs of `L` positions stepping by `C`. Each class is
then a separate kernel fact, exactly as the Wieferich classes are separate declarations. -/
public theorem sumB_split (f : ℕ → ℕ) (start C L : ℕ) :
    sumB f start (C * L) 1 = ∑ c ∈ range C, sumB f (c + start) L C := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.mul_succ, sumB_add, ih, sumB_eq_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [sumB_succ]
    have h : c * 1 + (C * L * 1 + start) = L * C + (c + start) := by ring
    rw [h]
    exact Nat.add_comm _ _

/-! ## The two summands

`recipAtK` reads the sieve bit first: the truncated quotient sits in the `true` branch of the
`Bool.rec`, so a clear bit contributes the literal `0`. `bitAtK` is the same shape with the
quotient replaced by `1`, and counts the positions that contribute. -/

/-- The scaled reciprocal at one sieve position: `S / value t` where the bit at `t` is set, `0`
where it is clear. -/
@[expose] public def recipAtK (s S t : ℕ) : ℕ :=
  (Sieve.testBitK s t).rec 0 (S.div (Sieve.valueK t))

/-- `1` where the sieve bit at `t` is set, `0` where it is clear. -/
@[expose] public def bitAtK (s t : ℕ) : ℕ :=
  (Sieve.testBitK s t).rec 0 1

@[simp, grind =] theorem recipAtK_eq (s S t : ℕ) :
    recipAtK s S t = if s.testBit t then S / Sieve.value t else 0 := by
  rw [recipAtK, Bool.rec_eq, Sieve.testBitK_eq_testBit, Sieve.valueK_eq_value, Nat.div_eq_div]

@[simp, grind =] theorem bitAtK_eq (s t : ℕ) : bitAtK s t = if s.testBit t then 1 else 0 := by
  rw [bitAtK, Bool.rec_eq, Sieve.testBitK_eq_testBit]

theorem bitAtK_le_one (s t : ℕ) : bitAtK s t ≤ 1 := by grind

/-- The count of contributing positions never exceeds the number of positions scanned, which is
the bound available without running a second fold. -/
public theorem sumB_bitAtK_le (s start len step : ℕ) : sumB (bitAtK s) start len step ≤ len := by
  induction len with
  | zero => simp
  | succ n ih =>
    rw [sumB_succ]
    have := bitAtK_le_one s ((n.mul step).add start)
    omega

/-! ## Numbers with no small factor

A sieve segment above the base range certifies that a surviving number has no prime factor up to the
base bound. Where the number is below the square of that bound, this makes it prime, which is what
the sum over a segment needs. -/

/-- A number below `B ^ 2` with no prime factor at most `B` is prime. -/
public theorem prime_of_no_small_factor {n B : ℕ} (hn : 2 ≤ n) (hB : n < B ^ 2)
    (h : ∀ q ≤ B, q.Prime → ¬ q ∣ n) : n.Prime := by
  by_contra hnp
  have hq : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hle : n.minFac ≤ B := by
    by_contra hgt
    have : B ^ 2 < n.minFac ^ 2 := Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  exact h n.minFac hle hq (Nat.minFac_dvd n)

/-! ## Positions that share a quotient

High up the sieve the truncated quotient `S / value t` is constant over long runs of positions, so
the run contributes that quotient once per set bit and needs only the count of set bits, not one
division per bit. `sumB_recipAtK_const` is that trade, and `sumB_recipAtK_const_ends` reduces its
hypothesis to the two ends of the run, since `value` increases and so the quotient decreases. -/

theorem recipAtK_eq_mul {s S k t : ℕ} (h : S / Sieve.value t = k) :
    recipAtK s S t = k * bitAtK s t := by
  rw [recipAtK_eq, bitAtK_eq, h]
  split <;> simp

/-- Where every position of the run has quotient `k`, the reciprocal fold is `k` times the count
fold. -/
public theorem sumB_recipAtK_const (s S k lo len : ℕ)
    (h : ∀ i < len, S / Sieve.value (i + lo) = k) :
    sumB (recipAtK s S) lo len 1 = k * sumB (bitAtK s) lo len 1 := by
  induction len with
  | zero => simp
  | succ n ih =>
    rw [sumB_succ, sumB_succ, Nat.mul_add, ih fun i hi ↦ h i (Nat.lt_succ_of_lt hi)]
    have hn : S / Sieve.value ((n.mul 1).add lo) = k := by
      have := h n (Nat.lt_succ_self n)
      simpa using this
    rw [recipAtK_eq_mul hn]

/-- The hypothesis of `sumB_recipAtK_const` from the two ends of the run alone, with the product
handed back as the literal `a`. -/
public theorem sumB_recipAtK_const_ends (s S k lo len c a : ℕ)
    (h₁ : Nat.beq (S / Sieve.value lo) k = true)
    (h₂ : Nat.beq (S / Sieve.value (lo + (len - 1))) k = true)
    (hc : sumB (bitAtK s) lo len 1 = c)
    (ha : Nat.beq (Nat.mul k c) a = true) :
    sumB (recipAtK s S) lo len 1 = a := by
  rw [Nat.beq_eq] at ha
  rw [← ha, ← hc]
  refine sumB_recipAtK_const s S k lo len fun i hi ↦ ?_
  rw [Nat.beq_eq] at h₁ h₂
  have hlo : Sieve.value lo ≤ Sieve.value (i + lo) :=
    Sieve.value_strictMono.monotone (by omega)
  have hhi : Sieve.value (i + lo) ≤ Sieve.value (lo + (len - 1)) :=
    Sieve.value_strictMono.monotone (by omega)
  have h0 : 0 < Sieve.value lo := by rw [Sieve.value]; omega
  have h1 : 0 < Sieve.value (i + lo) := by rw [Sieve.value]; omega
  have hup : S / Sieve.value (i + lo) ≤ k := h₁ ▸ Nat.div_le_div_left hlo h0
  have hdown : k ≤ S / Sieve.value (i + lo) := h₂ ▸ Nat.div_le_div_left hhi h1
  omega

/-! ## The exact rational sum over the scanned positions -/

/-- The exact sum of `1 / value t` over the positions of the scan whose sieve bit is set. -/
public noncomputable def recipSum (s start len step : ℕ) : ℚ :=
  ∑ n ∈ range len,
    if s.testBit (n * step + start) then (Sieve.value (n * step + start) : ℚ)⁻¹ else 0

theorem value_ne_zero (k : ℕ) : Sieve.value k ≠ 0 := by
  rw [Sieve.value]
  omega

/-- The exact sum is additive along a split of the scan, the `ℚ` counterpart of `sumB_add`. A
segmented scan needs both: `sumB_add` to join the kernel literals, this to join the bounds. -/
public theorem recipSum_add (s start a b step : ℕ) :
    recipSum s start (a + b) step
      = recipSum s start a step + recipSum s (a * step + start) b step := by
  rw [recipSum, recipSum, recipSum, Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have h : (a + n) * step + start = n * step + (a * step + start) := by ring
  rw [h]

/-! ### The error bound

One truncation of size less than `1` per *contributing* position, not per position scanned. This
is the only change from the harmonic-number bound, where every position contributes: the error
term is the count fold `sumB (bitAtK s) …`, and `sumB_bitAtK_le` weakens it back to `len` when a
second fold is not wanted. -/

theorem div_le_inv {S v : ℕ} (hS : S ≠ 0) : ((S / v : ℕ) : ℚ) / S ≤ (v : ℚ)⁻¹ := by
  have hS' : (0 : ℚ) < S := by exact_mod_cast Nat.pos_of_ne_zero hS
  rw [div_le_iff₀ hS', inv_mul_eq_div]
  exact Nat.cast_div_le

theorem inv_le_div_succ {S v : ℕ} (hS : S ≠ 0) (hv : v ≠ 0) :
    (v : ℚ)⁻¹ ≤ (((S / v : ℕ) : ℚ) + 1) / S := by
  have hS' : (0 : ℚ) < S := by exact_mod_cast Nat.pos_of_ne_zero hS
  have hv' : (0 : ℚ) < v := by exact_mod_cast Nat.pos_of_ne_zero hv
  rw [le_div_iff₀ hS', inv_mul_eq_div, div_le_iff₀ hv']
  have h : S ≤ (S / v + 1) * v := by
    rw [Nat.mul_comm]
    exact (Nat.lt_mul_div_succ S (Nat.pos_of_ne_zero hv)).le
  exact_mod_cast h

/-- Lower bound: the truncated fold, rescaled, never overshoots the exact sum. -/
public theorem sumB_recipAtK_div_le {S : ℕ} (s start len step : ℕ) (hS : S ≠ 0) :
    ((sumB (recipAtK s S) start len step : ℕ) : ℚ) / S ≤ recipSum s start len step := by
  rw [recipSum, sumB_eq_sum, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  rw [recipAtK_eq]
  split
  · exact_mod_cast div_le_inv (v := Sieve.value (n * step + start)) hS
  · simp

/-- Upper bound: the fold plus one unit per contributing position, rescaled, is never below the
exact sum. -/
public theorem le_sumB_recipAtK_div {S : ℕ} (s start len step : ℕ) (hS : S ≠ 0) :
    recipSum s start len step
      ≤ (((sumB (recipAtK s S) start len step : ℕ) : ℚ)
          + ((sumB (bitAtK s) start len step : ℕ) : ℚ)) / S := by
  rw [recipSum, sumB_eq_sum, sumB_eq_sum, Nat.cast_sum, Nat.cast_sum, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_le_sum fun n _ ↦ ?_
  rw [recipAtK_eq, bitAtK_eq]
  split
  · push_cast
    exact inv_le_div_succ hS (value_ne_zero _)
  · simp

/-- The scan puts the exact sum in a closed rational interval whose width is the number of
contributing positions divided by the scale. -/
public theorem recipSum_mem_Icc {S : ℕ} (s start len step : ℕ) (hS : S ≠ 0) :
    recipSum s start len step ∈ Set.Icc
      (((sumB (recipAtK s S) start len step : ℕ) : ℚ) / S)
      ((((sumB (recipAtK s S) start len step : ℕ) : ℚ)
        + ((sumB (bitAtK s) start len step : ℕ) : ℚ)) / S) :=
  ⟨sumB_recipAtK_div_le s start len step hS, le_sumB_recipAtK_div s start len step hS⟩

/-! ## Identifying the scanned sum with a sum over primes -/

/-- A sieve for `N` serves any smaller bound, with the comparison as a `Bool` literal. -/
public theorem Sieve.IsSieve.monoB {N M s : ℕ} (h : Sieve.IsSieve N s) (hM : Nat.ble M N = true) :
    Sieve.IsSieve M s := fun t ht hv ↦ h t ht (hv.trans (Nat.ble_eq .. ▸ hM))

theorem Sieve.IsSieve.mono {N M s : ℕ} (h : Sieve.IsSieve N s) (hM : M ≤ N) :
    Sieve.IsSieve M s := fun t ht hv ↦ h t ht (hv.trans hM)

theorem recipSum_eq_Icc (s len : ℕ) :
    recipSum s 1 len 1
      = ∑ t ∈ Finset.Icc 1 len, if s.testBit t then (Sieve.value t : ℚ)⁻¹ else 0 := by
  rw [recipSum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.mul_one, Nat.add_comm]

theorem recipSum_eq_Icc_range (s lo len : ℕ) :
    recipSum s lo len 1
      = ∑ t ∈ Finset.Ico lo (lo + len), if s.testBit t then (Sieve.value t : ℚ)⁻¹ else 0 := by
  rw [recipSum, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.mul_one, Nat.add_comm]

/-- The scan of the positions `lo … lo + len - 1` sums the reciprocals of exactly the primes
between the numbers at its two ends, given that the bit at each position of the scan says whether
its number is prime. The sieve range uses this with `lo = 1`; a segment above the sieve uses it
with the segment's own first position. -/
public theorem recipSum_eq_primeSum_range {s lo len : ℕ} (hlo : 1 ≤ lo)
    (hbit : ∀ t, lo ≤ t → t < lo + len → (s.testBit t ↔ (Sieve.value t).Prime)) :
    recipSum s lo len 1
      = ∑ p ∈ (Finset.Ico (Sieve.value lo) (Sieve.value (lo + len))).filter Nat.Prime,
          (p : ℚ)⁻¹ := by
  rw [recipSum_eq_Icc_range, ← Finset.sum_filter]
  refine Finset.sum_nbij' (i := Sieve.value) (j := Sieve.index) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht ⊢
    obtain ⟨⟨h1, h2⟩, hbit'⟩ := ht
    refine ⟨⟨Sieve.value_strictMono.monotone h1, Sieve.value_strictMono h2⟩, ?_⟩
    exact (hbit t h1 h2).mp hbit'
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
    obtain ⟨⟨hlow, hhigh⟩, hprime⟩ := hp
    have h5 : 5 ≤ Sieve.value lo := Sieve.five_le_value (by omega)
    have hc : p % 6 = 1 ∨ p % 6 = 5 := hprime.mod_six_eq_one_or_five (by omega) (by omega)
    have hv : Sieve.value (Sieve.index p) = p := Sieve.value_index hc
    have h1 : lo ≤ Sieve.index p := by
      by_contra hcon
      have : Sieve.value (Sieve.index p) < Sieve.value lo :=
        Sieve.value_strictMono (by omega)
      omega
    have h2 : Sieve.index p < lo + len := by
      by_contra hcon
      have : Sieve.value (lo + len) ≤ Sieve.value (Sieve.index p) :=
        Sieve.value_strictMono.monotone (by omega)
      omega
    refine ⟨⟨h1, h2⟩, (hbit _ h1 h2).mpr ?_⟩
    rw [hv]
    exact hprime
  · intro t _
    exact Sieve.index_value t
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    have h5 : 5 ≤ Sieve.value lo := Sieve.five_le_value (by omega)
    exact Sieve.value_index (hp.2.mod_six_eq_one_or_five (by omega) (by omega))
  · intro t _
    rfl

/-- The unit-step scan of the positions `1 … len` of a sieve for `N` sums the reciprocals of
exactly the primes between `5` and `N`, provided `len` is the last position inside `N`. -/
public theorem recipSum_eq_primeSum {N s len : ℕ} (hs : Sieve.IsSieve N s)
    (hlen : Sieve.value len ≤ N) (hlen' : N < Sieve.value (len + 1)) :
    recipSum s 1 len 1 = ∑ p ∈ (Finset.Icc 5 N).filter Nat.Prime, (p : ℚ)⁻¹ := by
  rw [recipSum_eq_Icc, ← Finset.sum_filter]
  refine Finset.sum_nbij' (i := Sieve.value) (j := Sieve.index) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht ⊢
    obtain ⟨⟨h1, h2⟩, hbit⟩ := ht
    have hle : Sieve.value t ≤ N := (Sieve.value_strictMono.monotone h2).trans hlen
    exact ⟨⟨Sieve.five_le_value (by omega), hle⟩, (hs t (by omega) hle).mp hbit⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨h5, hN⟩, hprime⟩ := hp
    have hc : p % 6 = 1 ∨ p % 6 = 5 := hprime.mod_six_eq_one_or_five (by omega) (by omega)
    have hv : Sieve.value (Sieve.index p) = p := Sieve.value_index hc
    have h1 : 1 ≤ Sieve.index p := by
      rcases Nat.eq_zero_or_pos (Sieve.index p) with h | h
      · rw [h] at hv
        simp [Sieve.value] at hv
        omega
      · exact h
    have h2 : Sieve.index p ≤ len := by
      by_contra hcon
      have : Sieve.value (len + 1) ≤ Sieve.value (Sieve.index p) :=
        Sieve.value_strictMono.monotone (by omega)
      omega
    have hvN : Sieve.value (Sieve.index p) ≤ N := by
      rw [hv]
      exact hN
    refine ⟨⟨h1, h2⟩, (hs _ (by omega) hvN).mpr ?_⟩
    rw [hv]
    exact hprime
  · intro t _
    exact Sieve.index_value t
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    exact Sieve.value_index (hp.2.mod_six_eq_one_or_five (by omega) (by omega))
  · intro t _
    rfl

/-- Splitting off the two primes the mod-6 wheel does not carry. -/
public theorem primeSum_eq {N : ℕ} (hN : 5 ≤ N) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℚ)⁻¹
      = (2 : ℚ)⁻¹ + (3 : ℚ)⁻¹ + ∑ p ∈ (Finset.Icc 5 N).filter Nat.Prime, (p : ℚ)⁻¹ := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.range_eq_Ico,
    ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le 5) (by omega : 5 ≤ N + 1)]
  have h0 : ¬ Nat.Prime 0 := by norm_num
  have h1 : ¬ Nat.Prime 1 := by norm_num
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h4 : ¬ Nat.Prime 4 := by norm_num
  congr 1
  rw [← Finset.range_eq_Ico]
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4]

/-! ## Staging one fold across declarations

The three lemmas below are what `run_harmonic` splices. `sumB_seed` opens the chain with an empty
accumulator; each `sumB_chain` link consumes one kernel-checked batch equation
`Nat.beq (acc + sumB f start len step) acc' = true` and moves the running total forward;
`sumB_last` closes it. Every binder is explicit so that the emitter can supply them positionally.

The batch equations are separate declarations, so each one's kernel reduction covers one batch
rather than the whole fold, and a wrong literal from the compiled twin makes its `Nat.beq` reduce
to `false` and the kernel reject the batch. -/

/-- Open a chain: the fold is its own value on top of an empty accumulator. -/
public theorem sumB_seed (f : ℕ → ℕ) (start len step : ℕ) :
    sumB f start len step = Nat.add 0 (sumB f start len step) :=
  (Nat.zero_add _).symm

/-- One chain link: a kernel-checked batch equation moves the running total forward by `len`
positions, leaving `rest` to go. -/
public theorem sumB_chain (f : ℕ → ℕ) (L start step len rest acc acc' : ℕ)
    (hP : L = Nat.add acc (sumB f start (Nat.add len rest) step))
    (h : Nat.beq (Nat.add acc (sumB f start len step)) acc' = true) :
    L = Nat.add acc' (sumB f (Nat.add (Nat.mul len step) start) rest step) := by
  grind [sumB_add, Nat.beq_eq]

/-- Close a chain: with no positions left, the batch equation gives the value of the whole fold. -/
public theorem sumB_last (f : ℕ → ℕ) (L start step len acc acc' : ℕ)
    (hP : L = Nat.add acc (sumB f start len step))
    (h : Nat.beq (Nat.add acc (sumB f start len step)) acc' = true) :
    L = acc' := by
  grind [Nat.beq_eq]

/-! ## Splitting one fold into residue classes of the position

`run_harmonic_classes` cuts the unit-step run of `C * L + R` positions from `1` into the `C` runs of
`L` positions stepping by `C`, one per residue class of the position modulo `C`, followed by the
`R` positions left over. Each class is its own chain of batches. `classAcc_step` adds the class
totals one at a time, so the emitted proof never unfolds a `Finset` sum. -/

/-- The first `k` of the `C` classes, each a run of `L` positions from `c + start` stepping by
`C`. -/
@[expose] public def classAcc (f : ℕ → ℕ) (start L C k : ℕ) : ℕ :=
  ∑ c ∈ range k, sumB f (Nat.add c start) L C

/-- Open the class chain: no classes added yet. -/
public theorem classAcc_zero (f : ℕ → ℕ) (start L C : ℕ) : classAcc f start L C 0 = 0 := by
  simp [classAcc]

/-- One class link: the class total `a` and a kernel-checked addition move the running total from
the first `k` classes to the first `k + 1`. -/
public theorem classAcc_step (f : ℕ → ℕ) (start L C k acc a acc' : ℕ)
    (h : classAcc f start L C k = acc) (hc : sumB f (Nat.add k start) L C = a)
    (hadd : Nat.beq (Nat.add acc a) acc' = true) :
    classAcc f start L C (Nat.add k 1) = acc' := by
  have e : classAcc f start L C (Nat.add k 1)
      = classAcc f start L C k + sumB f (Nat.add k start) L C := by
    simp only [classAcc, Nat.add_eq, Finset.sum_range_succ]
  grind [Nat.beq_eq]

/-- The classes `a … a + n - 1`, each a run of `L` positions from `(a + c) + start` stepping by
`C`. Blocks of classes let the class totals be added in two levels, so no chain of links grows
with the number of classes. -/
@[expose] public def classBlock (f : ℕ → ℕ) (start L C a n : ℕ) : ℕ :=
  ∑ c ∈ range n, sumB f (Nat.add (Nat.add a c) start) L C

/-- Open a block: no classes added yet. -/
public theorem classBlock_zero (f : ℕ → ℕ) (start L C a : ℕ) :
    classBlock f start L C a 0 = 0 := by
  simp [classBlock]

/-- One link inside a block: the class total `x` of class `a + n` and a kernel-checked addition move
the block's running total forward by one class. -/
public theorem classBlock_step (f : ℕ → ℕ) (start L C a n acc x acc' : ℕ)
    (h : classBlock f start L C a n = acc)
    (hc : sumB f (Nat.add (Nat.add a n) start) L C = x)
    (hadd : Nat.beq (Nat.add acc x) acc' = true) :
    classBlock f start L C a (Nat.add n 1) = acc' := by
  have e : classBlock f start L C a (Nat.add n 1)
      = classBlock f start L C a n + sumB f (Nat.add (Nat.add a n) start) L C := by
    simp only [classBlock, Nat.add_eq, Finset.sum_range_succ]
  grind [Nat.beq_eq]

/-- One link between blocks: the first `a` classes followed by the block of the next `n`. -/
public theorem classAcc_block (f : ℕ → ℕ) (start L C a n acc x acc' : ℕ)
    (h : classAcc f start L C a = acc) (hb : classBlock f start L C a n = x)
    (hadd : Nat.beq (Nat.add acc x) acc' = true) :
    classAcc f start L C (Nat.add a n) = acc' := by
  have e : classAcc f start L C (Nat.add a n)
      = classAcc f start L C a + classBlock f start L C a n := by
    simp only [classAcc, classBlock, Nat.add_eq, Finset.sum_range_add]
  grind [Nat.beq_eq]

/-- The unit-step run of `C * L + R` positions from `1` is its `C` classes followed by the `R`
positions left over. -/
public theorem sumB_classSplit (f : ℕ → ℕ) (C L R : ℕ) :
    sumB f 1 (Nat.add (Nat.mul C L) R) 1
      = Nat.add (classAcc f 1 L C C) (sumB f (Nat.add (Nat.mul C L) 1) R 1) := by
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [sumB_add, sumB_split, Nat.mul_one]
  simp only [classAcc, Nat.add_eq]

/-- Close the class split: the chained class total, the leftover run and one kernel-checked
addition give the value of the whole fold. -/
public theorem sumB_classSplit_close (f : ℕ → ℕ) (C L R A1 A2 A : ℕ)
    (hacc : classAcc f 1 L C C = A1) (hrem : sumB f (Nat.add (Nat.mul C L) 1) R 1 = A2)
    (hsum : Nat.beq (Nat.add A1 A2) A = true) :
    sumB f 1 (Nat.add (Nat.mul C L) R) 1 = A := by
  rw [sumB_classSplit, hacc, hrem]
  grind [Nat.beq_eq]

/-! ## Reading each batch through a window of the sieve

`run_harmonic_window` gives every batch of `B` consecutive positions from `lo` its own literal `w`,
the `B` bits of the sieve from position `lo`, certified once by
`Nat.beq (Nat.land (Nat.shiftRight s lo) (Nat.sub (Nat.shiftLeft 1 B) 1)) w = true`. The batch
folds then read bit `i` of `w` for the position `lo + i`, and `recip_window` and `bit_window`
identify each windowed batch with the same batch read from the whole sieve. -/

/-- The scaled reciprocal at position `lo + i`, reading bit `i` of the window `w`. -/
@[expose] public def recipAtW (w lo S i : ℕ) : ℕ :=
  (Sieve.testBitK w i).rec 0 (S.div (Sieve.valueK (Nat.add lo i)))

/-- `1` where bit `i` of the window `w` is set, `0` where it is clear. -/
@[expose] public def bitAtW (w i : ℕ) : ℕ :=
  (Sieve.testBitK w i).rec 0 1

theorem window_testBit {s lo B w i : ℕ}
    (hw : Nat.beq (Nat.land (Nat.shiftRight s lo) (Nat.sub (Nat.shiftLeft 1 B) 1)) w = true)
    (hi : i < B) : w.testBit i = s.testBit (lo + i) := by
  rw [Nat.beq_eq] at hw
  subst hw
  simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.sub_eq,
    Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  simp [hi]

/-- A windowed batch of the reciprocal fold is the same batch read from the whole sieve. -/
public theorem recip_window (s S lo B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight s lo) (Nat.sub (Nat.shiftLeft 1 B) 1)) w = true) :
    sumB (recipAtK s S) lo B 1 = sumB (recipAtW w lo S) 0 B 1 := by
  rw [sumB_eq_sum, sumB_eq_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hb := window_testBit hw (Finset.mem_range.mp hi)
  rw [Nat.mul_one, Nat.add_zero, Nat.add_comm i lo, recipAtK_eq, recipAtW, Bool.rec_eq,
    Sieve.testBitK_eq_testBit, Sieve.valueK_eq_value, Nat.div_eq_div, Nat.add_eq, hb]

/-- `recip_window` with its numerals written as raw literals, so that the window certificate the
emitter declares is the very term this hypothesis asks for. -/
public theorem recip_windowR (s S lo B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight s lo)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) B) (nat_lit 1))) w = true) :
    sumB (recipAtK s S) lo B (nat_lit 1)
      = sumB (recipAtW w lo S) (nat_lit 0) B (nat_lit 1) :=
  recip_window s S lo B w hw

/-- A windowed batch of the count fold is the same batch read from the whole sieve. -/
public theorem bit_window (s lo B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight s lo) (Nat.sub (Nat.shiftLeft 1 B) 1)) w = true) :
    sumB (bitAtK s) lo B 1 = sumB (bitAtW w) 0 B 1 := by
  rw [sumB_eq_sum, sumB_eq_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hb := window_testBit hw (Finset.mem_range.mp hi)
  rw [Nat.mul_one, Nat.add_zero, Nat.add_comm i lo, bitAtK_eq, bitAtW, Bool.rec_eq,
    Sieve.testBitK_eq_testBit, hb]

/-- `bit_window` with its numerals written as raw literals. -/
public theorem bit_windowR (s lo B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight s lo)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) B) (nat_lit 1))) w = true) :
    sumB (bitAtK s) lo B (nat_lit 1) = sumB (bitAtW w) (nat_lit 0) B (nat_lit 1) :=
  bit_window s lo B w hw

/-- One windowed batch as its own equation: the batch of `len` positions from `start` equals the
fold `g` over `0 … len - 1`, whose kernel-checked value is `t`. Declaring this on its own keeps the
bridge out of the chain, so no declaration carries both a bridge and a chain. -/
public theorem sumB_windowEq (f g : ℕ → ℕ) (start len t : ℕ)
    (hb : sumB f start len 1 = sumB g 0 len 1)
    (h : Nat.beq (sumB g 0 len 1) t = true) :
    sumB f start len 1 = t := by
  grind [Nat.beq_eq]

/-- `sumB_windowEq` with its numerals written as raw literals, the form the emitter builds. The two
say the same thing; which one the emitter uses decides whether the statement it declares and the
binder it hands that statement to are the same term. -/
public theorem sumB_windowEqR (f g : ℕ → ℕ) (start len t : ℕ)
    (hb : sumB f start len (nat_lit 1) = sumB g (nat_lit 0) len (nat_lit 1))
    (h : Nat.beq (sumB g (nat_lit 0) len (nat_lit 1)) t = true) :
    sumB f start len (nat_lit 1) = t := by
  grind [Nat.beq_eq]

/-- One chain link through a bridge: the batch of `len` positions from `start` equals a fold `g`
over `0 … len - 1`, and a kernel-checked batch equation on `g` moves the running total forward. -/
public theorem sumB_chainVia (f g : ℕ → ℕ) (L start step len rest acc acc' : ℕ)
    (hP : L = Nat.add acc (sumB f start (Nat.add len rest) step))
    (hb : sumB f start len step = sumB g 0 len 1)
    (h : Nat.beq (Nat.add acc (sumB g 0 len 1)) acc' = true) :
    L = Nat.add acc' (sumB f (Nat.add (Nat.mul len step) start) rest step) := by
  grind [sumB_add, Nat.beq_eq]

/-- Close a chain through a bridge. -/
public theorem sumB_lastVia (f g : ℕ → ℕ) (L start step len acc acc' : ℕ)
    (hP : L = Nat.add acc (sumB f start len step))
    (hb : sumB f start len step = sumB g 0 len 1)
    (h : Nat.beq (Nat.add acc (sumB g 0 len 1)) acc' = true) :
    L = acc' := by
  grind [Nat.beq_eq]

/-- Join two adjacent runs into one, with every position and length a plain literal checked by
`Nat.beq`. A tree of these puts exactly one join in each declaration. -/
public theorem sumB_join (f : ℕ → ℕ) (start step len₁ len₂ tot start₂ a₁ a₂ a : ℕ)
    (hstart : Nat.beq (Nat.add (Nat.mul len₁ step) start) start₂ = true)
    (htot : Nat.beq (Nat.add len₁ len₂) tot = true)
    (h₁ : sumB f start len₁ step = a₁)
    (h₂ : sumB f start₂ len₂ step = a₂)
    (hadd : Nat.beq (Nat.add a₁ a₂) a = true) :
    sumB f start tot step = a := by
  grind [sumB_add, Nat.beq_eq]

/-- One chain link whose every position and length is a plain literal: `tot` is the run still to go,
`start'` the next run's first position, both supplied as literals and checked by `Nat.beq`, so that
consecutive links match without the checker having to relate `start + len * step` to a literal. -/
public theorem sumB_chainEqL (f : ℕ → ℕ) (L start step len rest tot start' acc a acc' : ℕ)
    (hP : L = Nat.add acc (sumB f start tot step))
    (htot : Nat.beq (Nat.add len rest) tot = true)
    (hs : Nat.beq (Nat.add (Nat.mul len step) start) start' = true)
    (h : sumB f start len step = a)
    (hadd : Nat.beq (Nat.add acc a) acc' = true) :
    L = Nat.add acc' (sumB f start' rest step) := by
  grind [sumB_add, Nat.beq_eq]

/-- Close a chain of literal links. -/
public theorem sumB_lastEqL (f : ℕ → ℕ) (L start step len tot acc a acc' : ℕ)
    (hP : L = Nat.add acc (sumB f start tot step))
    (htot : Nat.beq len tot = true)
    (h : sumB f start len step = a)
    (hadd : Nat.beq (Nat.add acc a) acc' = true) :
    L = acc' := by
  grind [Nat.beq_eq]

/-- One chain link consuming a proved equation for a whole segment, for chaining segments of
batches rather than batches. -/
public theorem sumB_chainEq (f : ℕ → ℕ) (L start step len rest acc a acc' : ℕ)
    (hP : L = Nat.add acc (sumB f start (Nat.add len rest) step))
    (h : sumB f start len step = a) (hadd : Nat.beq (Nat.add acc a) acc' = true) :
    L = Nat.add acc' (sumB f (Nat.add (Nat.mul len step) start) rest step) := by
  grind [sumB_add, Nat.beq_eq]

/-- Close a chain of segments. -/
public theorem sumB_lastEq (f : ℕ → ℕ) (L start step len acc a acc' : ℕ)
    (hP : L = Nat.add acc (sumB f start len step))
    (h : sumB f start len step = a) (hadd : Nat.beq (Nat.add acc a) acc' = true) :
    L = acc' := by
  grind [Nat.beq_eq]

/-- A batch of a fold over a segment literal, read through a window of that literal. The segment's
own first position `lo` is carried along, since the numbers are still the ones at `lo + i`. -/
public theorem recipW_window (g S lo k B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight g k) (Nat.sub (Nat.shiftLeft 1 B) 1)) w = true) :
    sumB (recipAtW g lo S) k B 1 = sumB (recipAtW w (lo + k) S) 0 B 1 := by
  rw [sumB_eq_sum, sumB_eq_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hb := window_testBit hw (Finset.mem_range.mp hi)
  have hbit : g.testBit (i + k) = w.testBit i := by rw [Nat.add_comm i k, hb]
  have harg : lo + (i + k) = lo + k + i := by omega
  simp only [recipAtW, Bool.rec_eq, Sieve.testBitK_eq_testBit, Sieve.valueK_eq_value, Nat.add_eq,
    Nat.div_eq_div, Nat.mul_one, Nat.add_zero, hbit, harg]

/-- `recipW_window` with its numerals written as raw literals, the form the emitter builds. The
first position of the batch is taken as a literal of its own, since the emitter has it. -/
public theorem recipW_windowR (g S lo k lok B w : ℕ)
    (hlok : Nat.beq (Nat.add lo k) lok = true)
    (hw : Nat.beq (Nat.land (Nat.shiftRight g k)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) B) (nat_lit 1))) w = true) :
    sumB (recipAtW g lo S) k B (nat_lit 1)
      = sumB (recipAtW w lok S) (nat_lit 0) B (nat_lit 1) := by
  rw [Nat.beq_eq] at hlok
  subst hlok
  exact recipW_window g S lo k B w hw

/-- The count fold counterpart of `recipW_window`. -/
public theorem bitW_window (g k B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight g k) (Nat.sub (Nat.shiftLeft 1 B) 1)) w = true) :
    sumB (bitAtW g) k B 1 = sumB (bitAtW w) 0 B 1 := by
  rw [sumB_eq_sum, sumB_eq_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hb := window_testBit hw (Finset.mem_range.mp hi)
  have hbit : g.testBit (i + k) = w.testBit i := by rw [Nat.add_comm i k, hb]
  simp only [bitAtW, Bool.rec_eq, Sieve.testBitK_eq_testBit, Nat.mul_one, Nat.add_zero, hbit]

/-- `bitW_window` with its numerals written as raw literals. -/
public theorem bitW_windowR (g k B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight g k)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) B) (nat_lit 1))) w = true) :
    sumB (bitAtW g) k B (nat_lit 1) = sumB (bitAtW w) (nat_lit 0) B (nat_lit 1) :=
  bitW_window g k B w hw

/-! ## Reading a segment above the sieve

A segment literal `g` covering the numbers from `a` upward has bit `j` for the number at position
`index a + j`. Its bits say which of those numbers are prime as soon as two things hold: a set bit
means no prime factor up to the segment's divisor bound `B`, and a clear bit means there is one.
Shifting `g` up by `index a` puts it in the position the scan expects, and the shift lives only in
the proof, never in a literal the kernel has to build. -/

/-- Where the set bits of `g` are exactly the numbers of the segment with no prime factor up to `B`,
and every number of the segment lies between `B` and `B ^ 2`, the bits say which are prime. -/
public theorem segment_bit_iff {g B a W : ℕ}
    (hsound : ∀ j < W, g.testBit j = true →
      ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value (Sieve.index a + j))
    (hcomplete : ∀ j < W, (∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value (Sieve.index a + j)) →
      g.testBit j = true)
    (hlow : ∀ j < W, B < Sieve.value (Sieve.index a + j))
    (hhigh : ∀ j < W, Sieve.value (Sieve.index a + j) < B ^ 2) :
    ∀ j < W, (g.testBit j = true ↔ (Sieve.value (Sieve.index a + j)).Prime) := by
  intro j hj
  refine ⟨fun hset ↦ ?_, fun hp ↦ hcomplete j hj fun q hq hqp hdvd ↦ ?_⟩
  · refine prime_of_no_small_factor ?_ (hhigh j hj) (hsound j hj hset)
    have h1 := hlow j hj
    have h2 := hhigh j hj
    rcases Nat.eq_zero_or_pos B with rfl | hB
    · simp at h2
    · omega
  · have hqle : q ≤ Sieve.value (Sieve.index a + j) := Nat.le_of_dvd (by
      have := hlow j hj
      have := hqp.two_le
      omega) hdvd
    have := (Nat.Prime.eq_one_or_self_of_dvd hp q hdvd)
    have := hqp.two_le
    have := hlow j hj
    omega

/-- Shifting a segment literal up by `lo` makes the scan from `lo` read its bits in order. -/
theorem testBit_shiftLeft_add (g lo j : ℕ) :
    (Nat.shiftLeft g lo).testBit (lo + j) = g.testBit j := by
  simp [Nat.testBit_shiftLeft]

/-- The scan of the shifted segment is the windowed fold over the segment itself. -/
public theorem recip_shift (g S lo len : ℕ) :
    sumB (recipAtK (Nat.shiftLeft g lo) S) lo len 1 = sumB (recipAtW g lo S) 0 len 1 := by
  rw [sumB_eq_sum, sumB_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.mul_one, Nat.add_zero, Nat.add_comm i lo, recipAtK_eq, recipAtW, Bool.rec_eq,
    Sieve.testBitK_eq_testBit, Sieve.valueK_eq_value, Nat.div_eq_div, Nat.add_eq,
    testBit_shiftLeft_add]

/-- The count fold counterpart of `recip_shift`. -/
public theorem bit_shift (g lo len : ℕ) :
    sumB (bitAtK (Nat.shiftLeft g lo)) lo len 1 = sumB (bitAtW g) 0 len 1 := by
  rw [sumB_eq_sum, sumB_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.mul_one, Nat.add_zero, Nat.add_comm i lo, bitAtK_eq, bitAtW, Bool.rec_eq,
    Sieve.testBitK_eq_testBit, testBit_shiftLeft_add]

/-! ## Packaging a pair of chained folds as an interval

`PrimeRecipIcc` names the conclusion so that the emitter builds the emitted statement out of four
`Nat` literals and no typeclass instances at all. -/

/-- The sum of the reciprocals of the primes up to `N` lies in the interval of width `C / S`
above `5 / 6 + A / S`. -/
@[expose] public noncomputable def PrimeRecipIcc (N A C S : ℕ) : Prop :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℚ)⁻¹ ∈
    Set.Icc (5 / 6 + (A : ℚ) / S) (5 / 6 + ((A : ℚ) + (C : ℚ)) / S)

/-- The sum of the reciprocals of the primes in `a … b - 1` lies in the interval of width `C / S`
above `A / S`. A scan of the base sieve and a scan of a segment above it both land here, and
`primeRecipRange_add` joins two neighbouring ranges. -/
@[expose] public noncomputable def PrimeRecipRange (a b A C S : ℕ) : Prop :=
  ∑ p ∈ (Finset.Ico a b).filter Nat.Prime, (p : ℚ)⁻¹ ∈
    Set.Icc ((A : ℚ) / S) (((A : ℚ) + (C : ℚ)) / S)

/-- A scan of the positions `lo … lo + len - 1` encloses the sum over the primes it covers,
provided the bit at each scanned position says whether its number is prime. -/
public theorem primeRecipRange_of {s S lo len A C : ℕ} (hlo : 1 ≤ lo)
    (hS : Nat.blt 0 S = true)
    (hbit : ∀ t, lo ≤ t → t < lo + len → (s.testBit t ↔ (Sieve.value t).Prime))
    (hA : sumB (recipAtK s S) lo len 1 = A) (hC : sumB (bitAtK s) lo len 1 = C) :
    PrimeRecipRange (Sieve.value lo) (Sieve.value (lo + len)) A C S := by
  rw [Nat.blt_eq] at hS
  have hSne : S ≠ 0 := by omega
  have heq := recipSum_eq_primeSum_range hlo hbit
  have hmem := recipSum_mem_Icc (S := S) s lo len 1 hSne
  rw [heq, hA, hC] at hmem
  exact hmem

/-- Two neighbouring ranges of primes add, with the two totals and the two counts added as
literals. -/
public theorem primeRecipRange_add {a b c A₁ C₁ A₂ C₂ A C S : ℕ}
    (hab : Nat.ble a b = true) (hbc : Nat.ble b c = true)
    (h₁ : PrimeRecipRange a b A₁ C₁ S) (h₂ : PrimeRecipRange b c A₂ C₂ S)
    (hA : Nat.beq (Nat.add A₁ A₂) A = true) (hC : Nat.beq (Nat.add C₁ C₂) C = true) :
    PrimeRecipRange a c A C S := by
  rw [Nat.beq_eq] at hA hC
  rw [Nat.ble_eq] at hab hbc
  rw [PrimeRecipRange, Finset.sum_filter] at h₁ h₂ ⊢
  rw [← Finset.sum_Ico_consecutive _ hab hbc]
  obtain ⟨hlo₁, hhi₁⟩ := h₁
  obtain ⟨hlo₂, hhi₂⟩ := h₂
  subst hA
  subst hC
  simp only [Nat.add_eq]
  push_cast
  simp only [add_div] at hhi₁ hhi₂ ⊢
  exact ⟨by linarith, by linarith⟩

/-- One sieved segment above the base range, as an enclosure of the sum over the primes it covers.
`hseg` is the equation the segment command emits, and the two fold equations are the windowed folds
over the segment literal, which the batches and the tree of joins produce exactly as for the base
range. -/
public theorem primeRecipRange_segment {B a W S g A C : ℕ}
    (ha : a % 6 = 1 ∨ a % 6 = 5) (ha5 : 5 ≤ a) (hBa : B < a)
    (hS : Nat.blt 0 S = true)
    (htop : Sieve.value (Sieve.index a + W - 1) < B ^ 2)
    (hsound : ∀ j < W, g.testBit j = true →
      ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value (Sieve.index a + j))
    (hcomplete : ∀ j < W,
      (∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value (Sieve.index a + j)) → g.testBit j = true)
    (hA : sumB (recipAtW g (Sieve.index a) S) 0 W 1 = A)
    (hC : sumB (bitAtW g) 0 W 1 = C) :
    PrimeRecipRange a (Sieve.value (Sieve.index a + W)) A C S := by
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
    rw [testBit_shiftLeft_add]
    exact hiff j (by omega)
  have hA' : sumB (recipAtK (Nat.shiftLeft g (Sieve.index a)) S) (Sieve.index a) W 1 = A := by
    rw [recip_shift]
    exact hA
  have hC' : sumB (bitAtK (Nat.shiftLeft g (Sieve.index a))) (Sieve.index a) W 1 = C := by
    rw [bit_shift]
    exact hC
  have h1 : 1 ≤ Sieve.index a := by
    rw [Sieve.index]
    omega
  have := primeRecipRange_of h1 hS hbit hA' hC'
  rwa [hlo] at this

/-- Everything the segment command's output needs in one application: the base sieve, the equation
the command emits, numeric side conditions as `Bool` literals, and the two folds over the segment
literal. -/
public theorem primeRecipRange_of_segRun {s B a W S g A C lo next : ℕ} (hs : Sieve.IsSieve B s)
    (ha : Nat.mod a 6 = 1 ∨ Nat.mod a 6 = 5) (hB6 : Nat.mod B 6 = 1 ∨ Nat.mod B 6 = 5)
    (ha5 : Nat.ble 5 a = true) (hW : Nat.blt (W - 1) (2 ^ 32) = true)
    (hB1 : Nat.ble 1 B = true) (h7B : Nat.ble (7 * B) a = true)
    (hS : Nat.blt 0 S = true)
    (hlo : Nat.beq (Sieve.index a) lo = true)
    (htv : Nat.beq (Sieve.value (lo + W)) next = true)
    (htop : Nat.blt (Sieve.value (lo + W - 1)) (B ^ 2) = true)
    (hseg : Sieve.segRun s a W B = g)
    (hA : sumB (recipAtW g lo S) 0 W 1 = A)
    (hC : sumB (bitAtW g) 0 W 1 = C) :
    PrimeRecipRange a next A C S := by
  rw [Nat.beq_eq] at hlo htv
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
  refine primeRecipRange_segment ha ha5 (by omega) hS htop
    (fun j hj h ↦ hsound' j hj h) hcomplete' hA hC
public theorem primeRecipIcc_of {Nb N S s len A C : ℕ} (hs : Sieve.IsSieve Nb s)
    (hcov : Nat.ble N Nb = true) (hS : Nat.blt 0 S = true)
    (hlen : Nat.ble (Sieve.valueK len) N = true)
    (hlen' : Nat.blt N (Sieve.valueK (Nat.succ len)) = true)
    (h5 : Nat.ble 5 N = true)
    (hA : sumB (recipAtK s S) 1 len 1 = A)
    (hC : sumB (bitAtK s) 1 len 1 = C) :
    PrimeRecipIcc N A C S := by
  rw [Nat.ble_eq] at hcov hlen h5
  rw [Nat.blt_eq] at hS hlen'
  rw [Sieve.valueK_eq_value] at hlen hlen'
  have hSne : S ≠ 0 := by omega
  have heq := recipSum_eq_primeSum (len := len) (hs.mono hcov) hlen
    (by rwa [Nat.succ_eq_add_one] at hlen')
  have hmem := recipSum_mem_Icc (S := S) s 1 len 1 hSne
  rw [heq, hA, hC] at hmem
  have h23 : (2 : ℚ)⁻¹ + (3 : ℚ)⁻¹ = 5 / 6 := by norm_num
  rw [PrimeRecipIcc, primeSum_eq h5, h23]
  obtain ⟨hlo, hhi⟩ := hmem
  exact ⟨by linarith, by linarith⟩

/-- `primeRecipIcc_of` with the reciprocal fold alone: the count of contributing positions is at
most the number of positions scanned, so the interval has width `len / S`. -/
public theorem primeRecipIcc_of_single {Nb N S s len A : ℕ} (hs : Sieve.IsSieve Nb s)
    (hcov : Nat.ble N Nb = true) (hS : Nat.blt 0 S = true)
    (hlen : Nat.ble (Sieve.valueK len) N = true)
    (hlen' : Nat.blt N (Sieve.valueK (Nat.succ len)) = true)
    (h5 : Nat.ble 5 N = true)
    (hA : sumB (recipAtK s S) 1 len 1 = A) :
    PrimeRecipIcc N A len S := by
  have hC : sumB (bitAtK s) 1 len 1 ≤ len := sumB_bitAtK_le s 1 len 1
  have h := primeRecipIcc_of hs hcov hS hlen hlen' h5 hA rfl
  rw [PrimeRecipIcc] at h ⊢
  obtain ⟨hlo, hhi⟩ := h
  refine ⟨hlo, hhi.trans ?_⟩
  gcongr

/-! ## Packing both folds into one

With `P` above every possible reciprocal total, the summand `S / value t + P` at a set bit carries
the reciprocal fold in the residue of the packed total modulo `P` and the count fold in its
quotient, so one fold does the work of two. -/

/-- The packed summand: `S / value t + P` where the bit at `t` is set, `0` where it is clear. -/
@[expose] public def packAtK (s S P t : ℕ) : ℕ :=
  (Sieve.testBitK s t).rec 0 (Nat.add (S.div (Sieve.valueK t)) P)

theorem packAtK_eq (s S P t : ℕ) : packAtK s S P t = recipAtK s S t + P * bitAtK s t := by
  rw [packAtK, recipAtK_eq, bitAtK_eq, Bool.rec_eq, Sieve.testBitK_eq_testBit,
    Sieve.valueK_eq_value, Nat.div_eq_div, Nat.add_eq]
  split <;> simp

/-- The packed fold is the reciprocal fold plus `P` times the count fold. -/
public theorem sumB_pack (s S P start len step : ℕ) :
    sumB (packAtK s S P) start len step
      = sumB (recipAtK s S) start len step + P * sumB (bitAtK s) start len step := by
  rw [sumB_eq_sum, sumB_eq_sum, sumB_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ ↦ packAtK_eq s S P _

theorem recipAtK_le (s S t : ℕ) : recipAtK s S t ≤ S := by
  rw [recipAtK_eq]
  split
  · exact Nat.div_le_self _ _
  · exact Nat.zero_le _

/-- Each position contributes at most `S` to the reciprocal fold. -/
public theorem sumB_recipAtK_le (s S start len step : ℕ) :
    sumB (recipAtK s S) start len step ≤ len * S := by
  induction len with
  | zero => simp
  | succ n ih =>
    rw [sumB_succ, Nat.succ_mul]
    have := recipAtK_le s S ((n.mul step).add start)
    omega

/-- The packed summand at position `lo + i`, reading bit `i` of the window `w`. -/
@[expose] public def packAtW (w lo S P i : ℕ) : ℕ :=
  (Sieve.testBitK w i).rec 0 (Nat.add (S.div (Sieve.valueK (Nat.add lo i))) P)

/-- A windowed batch of the packed fold is the same batch read from the whole sieve. -/
public theorem pack_window (s S P lo B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight s lo) (Nat.sub (Nat.shiftLeft 1 B) 1)) w = true) :
    sumB (packAtK s S P) lo B 1 = sumB (packAtW w lo S P) 0 B 1 := by
  rw [sumB_eq_sum, sumB_eq_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hb := window_testBit hw (Finset.mem_range.mp hi)
  rw [Nat.mul_one, Nat.add_zero, Nat.add_comm i lo]
  simp only [packAtK, packAtW, Sieve.testBitK_eq_testBit, Nat.add_eq, hb]

/-- `pack_window` with its numerals written as raw literals. -/
public theorem pack_windowR (s S P lo B w : ℕ)
    (hw : Nat.beq (Nat.land (Nat.shiftRight s lo)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) B) (nat_lit 1))) w = true) :
    sumB (packAtK s S P) lo B (nat_lit 1)
      = sumB (packAtW w lo S P) (nat_lit 0) B (nat_lit 1) :=
  pack_window s S P lo B w hw

/-- `primeRecipIcc_of` from the packed fold alone: with `len * S < P`, its total `T` holds the
reciprocal fold as `T % P` and the count fold as `T / P`. -/
public theorem primeRecipIcc_of_pack {Nb N S P s len T : ℕ} (hs : Sieve.IsSieve Nb s)
    (hcov : Nat.ble N Nb = true) (hS : Nat.blt 0 S = true)
    (hlen : Nat.ble (Sieve.valueK len) N = true)
    (hlen' : Nat.blt N (Sieve.valueK (Nat.succ len)) = true)
    (h5 : Nat.ble 5 N = true) (hP : Nat.blt (Nat.mul len S) P = true)
    (hT : sumB (packAtK s S P) 1 len 1 = T) :
    PrimeRecipIcc N (T % P) (T / P) S := by
  rw [Nat.blt_eq, Nat.mul_eq] at hP
  have hlt : sumB (recipAtK s S) 1 len 1 < P := (sumB_recipAtK_le s S 1 len 1).trans_lt hP
  rw [sumB_pack] at hT
  have hA : sumB (recipAtK s S) 1 len 1 = T % P := by
    rw [← hT, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hC : sumB (bitAtK s) 1 len 1 = T / P := by
    rw [← hT, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, Nat.zero_add]
  exact primeRecipIcc_of hs hcov hS hlen hlen' h5 hA hC

/-! ## Counting and reading set bits with wide operations

A fold that visits every position costs one recursor step per position, and a recursor step costs
the same whatever it consumes. Both definitions here trade positions for wide `Nat` operations:
`popK` counts the set bits of a window in about twenty operations, and `recipBits` visits only the
set bits, taking its step count from `popK`. -/

/-- The mask with the low `ones` bits of every `period`-bit field set, `n` bits wide, written so
that the kernel builds it from four operations rather than reading a literal. -/
@[expose] public def maskK (n ones period : ℕ) : ℕ :=
  Nat.mul
    (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) period) (nat_lit 1)))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) ones) (nat_lit 1))

/-- The number of set bits of an `n`-bit window, by pairwise sums widening to 32-bit fields and a
digit sum. Valid while `n < 2 ^ 32 - 1`. -/
@[expose] public def popK (n w : ℕ) : ℕ :=
  let x1 := Nat.sub w (Nat.land (Nat.shiftRight w (nat_lit 1)) (maskK n (nat_lit 1) (nat_lit 2)))
  let x2 := Nat.add (Nat.land x1 (maskK n (nat_lit 2) (nat_lit 4)))
    (Nat.land (Nat.shiftRight x1 (nat_lit 2)) (maskK n (nat_lit 2) (nat_lit 4)))
  let x3 := Nat.land (Nat.add x2 (Nat.shiftRight x2 (nat_lit 4))) (maskK n (nat_lit 4) (nat_lit 8))
  let x4 := Nat.land (Nat.add x3 (Nat.shiftRight x3 (nat_lit 8))) (maskK n (nat_lit 8) (nat_lit 16))
  let x5 := Nat.land (Nat.add x4 (Nat.shiftRight x4 (nat_lit 16)))
    (maskK n (nat_lit 16) (nat_lit 32))
  Nat.mod x5 (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 32)) (nat_lit 1))

/-- Field `2 ^ i % 2053` of this number holds `i`, eleven bits to a field, for every `i < 2048`.
The powers of two are distinct modulo `2053`, so a lowest set bit names its own position. -/
@[expose] public def lsbTable : ℕ := 725139929340121427579112308344450704212126804527006297091421380149372318078889038960399924017393899934810265222679460841126934241169729415454329089221211084505528905340434999562864862297359524416255595066500285188641224769228880216438248203245260022308282550623010020508276056462535164432801470906630990257846508950827103382399877350102334154586892305943495712253049037017367462084835857092790486544294668330099150098812139435510188462023267803318543977426050216016218508589163255860860148746839718756022362804369196680894135538552702543151660318199329063782963882784635980726043719008725121582998521030474043872004345546297298153754417204863504997633762525453237031255762727403279078027408779382125530924781310021073610229859531980800322875711525575054565733166238386628668442438648147818113863600688648850489107762809405682404480687207101881351063297456153930847188527931528558007783227767084376405163714177571276294730892278230817868438186406125369806671599162237947718160603301020853568741526208984598458932894168726546323520332769211909919161923991338255152210932443054255642118840773693507853571607725137681081583269129389495247911956653126311325746650339758185685981849561933454082426066242223072319837085981642279885913766677652527444871177458101577293096270510542251541036779128235932653747569651018998514158829335551688792853080565754251129341102921067847016364507606799946376651974643993538799173430506470495628041131652731279525650993319684875969143774202656320388382695354588911084988936217989523861915252846151791928308119497011846671646449617587606385058722186885248077960037840623282349181784761117952675526070388913695183136307174014791789733300925184445921772287584488730275196528826811429635879060463848973478523218707143490162526698968133212430880019501958279710833305281285066398966674417970384399824033438325353425248377505663460370577151450555344216157653784149694489501006690968490005873556332301488675853964696106712983767207613666091760050837074947690806787608787251349506349619310000793512733217118143877113475878033517908873481862537786526017025021297886050362774486716441279343663202073191037434640280360163660681030127893085717169339525744493568583407878534362550570719698543604612347693054220537796919303940555806102405282474969806429503162308764674007453973849778628872235394775253389673717881467328817436009956864524483145623781155740556442664954041735170990415948354083336763534662653325617801727387071640039281491754796827308379480603406044019796963677094855920161401876265358762152515053564639354970993276149196381264311890640376553489109395826577476873210776150442771717950036138625294897977243481750976477686982429181668667297178600331573988227503472208179844115876161411127111569408052636459613128394034853549096637910443735641300864492421573606896920899907454826366415137181674998783277451978880527449923181468964076202934294538016203027770150842642980235225285608106272960651352475958647455649873771926805142480374769749477250060621718102164221337404381254223105071300667293351727323761966179269067624759650920279361212711351094953767614330227338304317506264874230421751204323620976557355158720867878719451113921531125251858497062852783707345052465304437107923886262167830104062236985580192804608317394070101613297528349818001457610954776629811376619838019909764816457844219770089998481342175311307225142844679594944827670711892802436166248749385126001185901092933989610237125209101535942320735827704870181820197108604038549472155827726323903347447853811844498241572792913584285892175054309713219392082441609057077983100562720941135174341199627094123612574714865464997313083176360436063563602503307694426520829538517181128257643131193290607653990212764877077898251968835216309358032370674648425416477284492071171618388171838870190590319675904883428017267181941692248242168965057055522584903725686426926600655067153537154303360633400707559130480632650671381933291191972329074870096730231135457662959155240930665244462170787734432619412463420311195568482435616692130845468587583276886877541553261701561214479187655677331255466745358620706844040374083365754994376902934867492321201160177343438869598766744992786587300044290672463159758293167153701212754647511697690131017651200935895253677764157007936682182442749791969838499092550045706531839285412611218311595386140791844948656650461057091528044976688614317074977314505830379033204895016282108877398512656707817709631227349189414508651642124720527045940811564303685225337895806650938174009187123730727518199782923122620725732906381726101669503280319623449960994883968600083631884570577469643414160788240516193724542966819200356302601279465586012903087081538157467815183503620820076583346718889727210398373281515413536692118196269297777845334384099695194698533024384139267565061036222659231947005052191239986223834657517416188870412759164178832993214206587358185924739865274713418790292868935010424098824487424850555839855045171314111554429924526200511249964786236832162006345868015292251587021397422041136852728116493788797802269413423542900179548447763717642980813610963193294844164290732030594511466944507586940059801031249665796045564955170473507823569954759155333448001177729238996204056149946697835863620010428335291693974381446218757059861046520764734051950856281129914637372727325393600732437380538282744878819849385255035152387561529228289396827740876812320779133940861957942947346618267047809070109044376870162921104614680703890194582375403831041795392082229762345332933910582486434012196135546683271497996919285141047029567014045842681526571802090958560585489915805007815939279150367540411450785050611674030762527742183693494664951351433837902308441917694334349639500190172774251313427605059506120389410905971457092850178214066779016034367076380832945721193027648034711153309685501369922850396559273328617317314491843881798541304987158265667053848132844998318969402926556692312767244768155196421691847523967132157011527380338073423663571940771869882754216142308983099194269681511375699027896973143440321171150231426537034575844225482489132752536365935112199248593942642321891867981514151483138807958474303529246805661464679630407452782657451393211488134100799686191858330076522184643699720804608965680994172552031260994632154924589296521268032970969392959726113801615071001952472491357193975424908861511261290611330681820559463581452497723301470435512787651729051904252134900431461442639153992376105498348050973662259053040490261238415569782716134097573439013066279398167135888327161346103743143795921517758582754617843623064086685775533154557622396262426903281575043746425408368416918545886801226100021966801069478671514263833214471217618366477948306269171883247830906126186770716362929085189280903990824426377669356169460762890695518643125454655525252367408304220861597211691718980709287425212416

/-- The position of a lowest set bit `l`, that is of a power of two below `2 ^ 2048`. -/
@[expose] public def lsbIdxK (l : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight lsbTable (Nat.mul (nat_lit 11) (Nat.mod l (nat_lit 2053))))
    (nat_lit 2047)

/-- The scaled reciprocals of the positions of the `c` lowest set bits of `w`, offset by `lo`. -/
@[expose] public def recipBits (lo S c w : ℕ) : ℕ :=
  c.rec (fun _ ↦ nat_lit 0)
    (fun _ ih v ↦
      Nat.add (Nat.div S (Sieve.valueK (Nat.add lo (lsbIdxK (Nat.sub v (Nat.land v (Nat.sub v (nat_lit 1))))))))
        (ih (Nat.land v (Nat.sub v (nat_lit 1)))))
    w

/-- The set-bit fold agrees with the fold over every position. -/
public theorem recipBits_eq (w lo S n : ℕ) (hw : Nat.blt w (Nat.shiftLeft (nat_lit 1) n) = true) :
    recipBits lo S (popK n w) w = sumB (recipAtW w lo S) (nat_lit 0) n (nat_lit 1) := by
  sorry

/-- The popcount agrees with the count fold. -/
public theorem popK_eq (w n : ℕ) (hw : Nat.blt w (Nat.shiftLeft (nat_lit 1) n) = true) :
    popK n w = sumB (bitAtW w) (nat_lit 0) n (nat_lit 1) := by
  sorry

/-- The count fold of a whole segment from one kernel-checked popcount. -/
public theorem count_of_popK (g W C : ℕ)
    (hw : Nat.blt g (Nat.shiftLeft (nat_lit 1) W) = true)
    (h : Nat.beq (popK W g) C = true) :
    sumB (bitAtW g) (nat_lit 0) W (nat_lit 1) = C := by
  sorry

/-- `sumB_windowEqR` reading a set-bit fold's certificate. -/
public theorem sumB_windowEqRBits (f : ℕ → ℕ) (w lo S start len t : ℕ)
    (hw : Nat.blt w (Nat.shiftLeft (nat_lit 1) len) = true)
    (hb : sumB f start len (nat_lit 1) = sumB (recipAtW w lo S) (nat_lit 0) len (nat_lit 1))
    (h : Nat.beq (recipBits lo S (popK len w) w) t = true) :
    sumB f start len (nat_lit 1) = t := by
  sorry

end PrimeCert
