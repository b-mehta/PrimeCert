/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.SieveCorrect
public import PrimeCert.SieveBase

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

@[simp, grind =] theorem sumB_zero (f : ℕ → ℕ) (start step : ℕ) : sumB f start 0 step = 0 := rfl

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

theorem Sieve.IsSieve.mono {N M s : ℕ} (h : Sieve.IsSieve N s) (hM : M ≤ N) :
    Sieve.IsSieve M s := fun t ht hv ↦ h t ht (hv.trans hM)

theorem recipSum_eq_Icc (s len : ℕ) :
    recipSum s 1 len 1
      = ∑ t ∈ Finset.Icc 1 len, if s.testBit t then (Sieve.value t : ℚ)⁻¹ else 0 := by
  rw [recipSum, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Nat.mul_one, Nat.add_comm]

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

/-! ## Packaging a pair of chained folds as an interval

`PrimeRecipIcc` names the conclusion so that the emitter builds the emitted statement out of four
`Nat` literals and no typeclass instances at all. -/

/-- The sum of the reciprocals of the primes up to `N` lies in the interval of width `C / S`
above `5 / 6 + A / S`. -/
@[expose] public noncomputable def PrimeRecipIcc (N A C S : ℕ) : Prop :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℚ)⁻¹ ∈
    Set.Icc (5 / 6 + (A : ℚ) / S) (5 / 6 + ((A : ℚ) + (C : ℚ)) / S)

/-- Everything `run_harmonic` needs in one application: a sieve covering `Nb ≥ N`, four numeric
side conditions as `Bool` literals, and the two chained fold equations. -/
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

end PrimeCert
