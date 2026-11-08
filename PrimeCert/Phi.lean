/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.PrimeHarmonic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The partial sum of reciprocals over numbers with no small factor

Bach, Klyve and Sorenson compute the sum of `1/p` over primes up to `x` from `φ(t, b)`, the sum of
`1/n` over `n ≤ t` whose least prime factor exceeds the `b`-th prime. This states the same
function by its sieving bound rather than by an index, which is the form the segmented sieve
already produces: `phiB t B` sums `1/n` over `n ≤ t` divisible by no prime at or below `B`.

`phiB_succ_prime` is the recurrence the identity is expanded by, and `phiB_succ_not_prime` says
the function only moves at primes.
-/

namespace PrimeCert

open Finset

/-- The `n ≤ t`, positive, with no prime factor at or below `B`. -/
public def phiSet (t B : ℕ) : Finset ℕ :=
  (range (t + 1)).filter fun n ↦ 0 < n ∧ ∀ q ≤ B, q.Prime → ¬ q ∣ n

/-- The sum of `1/n` over `phiSet t B`. -/
public noncomputable def phiB (t B : ℕ) : ℚ :=
  ∑ n ∈ phiSet t B, (n : ℚ)⁻¹

@[simp] public theorem mem_phiSet {t B n : ℕ} :
    n ∈ phiSet t B ↔ n ≤ t ∧ 0 < n ∧ ∀ q ≤ B, q.Prime → ¬ q ∣ n := by
  simp only [phiSet, mem_filter, mem_range, Nat.lt_succ_iff]

/-- Below the first prime nothing is sieved out, so `phiB` is the whole harmonic sum. -/
theorem phiSet_one (t : ℕ) : phiSet t 1 = (range (t + 1)).filter fun n ↦ 0 < n := by
  ext n
  simp only [mem_phiSet, mem_filter, mem_range, Nat.lt_succ_iff, and_congr_right_iff]
  intro _
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun q hq hp _ ↦ ?_⟩⟩
  have := hp.two_le
  omega

/-- At bound `1` nothing has been sieved out, so the value is the plain harmonic sum. This is the
leaf every branch of a full expansion ends at. -/
public theorem phiB_one (t : ℕ) :
    phiB t 1 = ∑ n ∈ (range (t + 1)).filter (fun n ↦ 0 < n), (n : ℚ)⁻¹ := by
  rw [phiB, phiSet_one]

/-- Once the bound reaches `t` only `1` survives, which is where the recursion bottoms out and
where the identity's trailing `- 1` comes from. -/
public theorem phiB_of_le {t B : ℕ} (ht : 0 < t) (h : t ≤ B) : phiB t B = 1 := by
  have hset : phiSet t B = {1} := by
    ext n
    simp only [mem_phiSet, mem_singleton]
    constructor
    · rintro ⟨hnt, hn0, hq⟩
      by_contra hne
      obtain ⟨q, hqp, hdvd⟩ := Nat.exists_prime_and_dvd hne
      exact hq q ((Nat.le_of_dvd hn0 hdvd).trans (hnt.trans h)) hqp hdvd
    · rintro rfl
      exact ⟨ht, one_pos, fun q _ hqp hdvd ↦ hqp.one_lt.ne' (Nat.dvd_one.mp hdvd)⟩
  rw [phiB, hset]
  simp

/-- Raising the bound past a composite removes nothing. -/
public theorem phiB_succ_not_prime {t B : ℕ} (h : ¬ (B + 1).Prime) :
    phiB t (B + 1) = phiB t B := by
  unfold phiB
  congr 1
  ext n
  simp only [mem_phiSet]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨fun hq q hqB ↦ hq q (by omega), ?_⟩
  intro hq q hqB hp
  rcases Nat.lt_or_ge q (B + 1) with hlt | hge
  · exact hq q (by omega) hp
  · have : q = B + 1 := by omega
    exact absurd (this ▸ hp) h

/-- Raising the bound across a stretch containing no prime removes nothing, so a derivation can
cross a prime gap in one step rather than one step per integer. -/
public theorem phiB_of_no_primes {t B B' : ℕ} (h : B' ≤ B)
    (hno : ∀ q, B' < q → q ≤ B → ¬ q.Prime) : phiB t B = phiB t B' := by
  revert hno
  induction B, h using Nat.le_induction with
  | base => intro _; rfl
  | succ n hn ih =>
    intro hno
    rw [phiB_succ_not_prime (hno (n + 1) (by omega) le_rfl)]
    exact ih fun q hq hq' ↦ hno q hq (by omega)

/-- The multiples of `p` surviving the bound below `p` are `p` times the survivors below `t / p`.
This is the step the identity's expansion rests on. -/
theorem phiSet_filter_dvd {t p : ℕ} (hp : p.Prime) :
    (phiSet t (p - 1)).filter (fun n ↦ p ∣ n)
      = (phiSet (t / p) (p - 1)).image (fun m ↦ p * m) := by
  have hp0 : 0 < p := hp.pos
  ext n
  simp only [mem_filter, mem_phiSet, mem_image]
  constructor
  · rintro ⟨⟨hnt, hn0, hq⟩, m, rfl⟩
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hn0
      · exact h
    refine ⟨m, ⟨?_, hm0, ?_⟩, rfl⟩
    · refine (Nat.le_div_iff_mul_le hp0).mpr ?_
      rw [Nat.mul_comm]
      exact hnt
    · intro q hq' hqp hdvd
      exact hq q hq' hqp (hdvd.mul_left p)
  · rintro ⟨m, ⟨hmt, hm0, hq⟩, rfl⟩
    refine ⟨⟨?_, Nat.mul_pos hp0 hm0, ?_⟩, m, rfl⟩
    · rw [Nat.mul_comm]
      exact Nat.mul_le_of_le_div p m t hmt
    · intro q hq' hqp hdvd
      rcases (Nat.Prime.dvd_mul hqp).mp hdvd with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hqp hp).mp h
        omega
      · exact hq q hq' hqp h

/-- The recurrence the identity is expanded by: raising the bound to a prime `p` removes the
multiples of `p`, whose reciprocals sum to `1 / p` times the function at `t / p`. -/
public theorem phiB_succ_prime {t p : ℕ} (hp : p.Prime) :
    phiB t p = phiB t (p - 1) - (p : ℚ)⁻¹ * phiB (t / p) (p - 1) := by
  have hp0 : 0 < p := hp.pos
  have hsub : phiSet t p = (phiSet t (p - 1)).filter (fun n ↦ ¬ p ∣ n) := by
    ext n
    simp only [mem_filter, mem_phiSet]
    constructor
    · rintro ⟨hnt, hn0, hq⟩
      exact ⟨⟨hnt, hn0, fun q hq' ↦ hq q (by omega)⟩, hq p le_rfl hp⟩
    · rintro ⟨⟨hnt, hn0, hq⟩, hnp⟩
      refine ⟨hnt, hn0, fun q hq' hqp hdvd ↦ ?_⟩
      rcases Nat.lt_or_ge q p with hlt | hge
      · exact hq q (by omega) hqp hdvd
      · have : q = p := by omega
        exact hnp (this ▸ hdvd)
  have hinj : Set.InjOn (fun m ↦ p * m) (phiSet (t / p) (p - 1)) :=
    fun a _ b _ hab ↦ Nat.eq_of_mul_eq_mul_left hp0 hab
  have hpt : ∀ m ∈ phiSet (t / p) (p - 1), ((p * m : ℕ) : ℚ)⁻¹ = (p : ℚ)⁻¹ * (m : ℚ)⁻¹ := by
    intro m _
    push_cast
    rw [mul_inv]
  rw [phiB, hsub, phiB, ← Finset.sum_filter_add_sum_filter_not (phiSet t (p - 1)) (fun n ↦ p ∣ n),
    phiSet_filter_dvd hp, Finset.sum_image hinj, Finset.sum_congr rfl hpt, phiB,
    Finset.mul_sum]
  ring

/-! ## Where the sieved sum becomes a sum over primes

A survivor that is composite needs two factors above the bound, so below `(B+1)^2` there are none
and the sieve has left exactly `1` and the primes above `B`. This is the step that turns `phiB`
back into the quantity being computed. -/

/-- Below `(B + 1) ^ 2` the only survivors are `1` and the primes above `B`. -/
public theorem phiSet_of_lt_sq {t B : ℕ} (ht : 0 < t) (h : t < (B + 1) * (B + 1)) :
    phiSet t B = insert 1 ((range (t + 1)).filter fun n ↦ n.Prime ∧ B < n) := by
  ext n
  simp only [mem_phiSet, mem_insert, mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hnt, hn0, hq⟩
    rcases eq_or_ne n 1 with rfl | hne
    · exact Or.inl rfl
    have hp : n.minFac.Prime := Nat.minFac_prime hne
    have hd : n.minFac ∣ n := Nat.minFac_dvd n
    have hpB : B < n.minFac := by
      by_contra hle
      exact hq n.minFac (by omega) hp hd
    obtain ⟨m, hm⟩ := hd
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rw [Nat.mul_zero] at hm
        omega
      · exact hpos
    have hm1 : m = 1 := by
      by_contra hmne
      have hr : m.minFac.Prime := Nat.minFac_prime hmne
      have hrd : m.minFac ∣ n := by
        rw [hm]
        exact (Nat.minFac_dvd m).mul_left _
      have hrB : B < m.minFac := by
        by_contra hle
        exact hq m.minFac (by omega) hr hrd
      have hrm : m.minFac ≤ m := Nat.minFac_le hm0
      have hle : (B + 1) * (B + 1) ≤ n := by
        rw [hm]
        exact Nat.mul_le_mul (by omega) (by omega)
      exact absurd (hle.trans hnt) (Nat.not_le.mpr h)
    rw [hm1, Nat.mul_one] at hm
    refine Or.inr ⟨hnt, ?_, ?_⟩
    · rw [hm]
      exact hp
    · rw [hm]
      exact hpB
  · rintro (rfl | ⟨hnt, hp, hB⟩)
    · exact ⟨ht, one_pos, fun q _ hqp hdvd ↦ hqp.one_lt.ne' (Nat.dvd_one.mp hdvd)⟩
    · refine ⟨hnt, hp.pos, fun q hq hqp hdvd ↦ ?_⟩
      have := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hdvd
      omega

/-- Below `(B + 1) ^ 2` the sieved sum is `1` plus the reciprocals of the primes above `B`. -/
public theorem phiB_of_lt_sq {t B : ℕ} (ht : 0 < t) (h : t < (B + 1) * (B + 1)) :
    phiB t B = 1 + ∑ p ∈ (range (t + 1)).filter (fun n ↦ n.Prime ∧ B < n), (p : ℚ)⁻¹ := by
  rw [phiB, phiSet_of_lt_sq ht h, Finset.sum_insert (by simp [Nat.not_prime_one])]
  norm_num

/-- The survivors counted by `phiB_of_lt_sq` are the primes of a range, which is the shape the
enclosure machinery already speaks in. -/
theorem filter_prime_eq_Ico {t B : ℕ} :
    (range (t + 1)).filter (fun n ↦ n.Prime ∧ B < n)
      = (Finset.Ico (B + 1) (t + 1)).filter Nat.Prime := by
  ext n
  simp only [mem_filter, mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hn, hp, hB⟩
    exact ⟨⟨by omega, hn⟩, hp⟩
  · rintro ⟨⟨hB, hn⟩, hp⟩
    exact ⟨hn, hp, by omega⟩

/-- A leaf below the square of its bound is answered by the range enclosure the emitter already
produces: the sum it needs is the prime range `B + 1 … t`, so no second evaluator is wanted. -/
public theorem phiB_mem_Icc_of_lt_sq {t B A C S : ℕ} (ht : 0 < t) (h : t < (B + 1) * (B + 1))
    (hr : PrimeRecipRange (B + 1) (t + 1) A C S) :
    phiB t B ∈ Set.Icc (1 + (A : ℚ) / S) (1 + ((A : ℚ) + (C : ℚ)) / S) := by
  rw [phiB_of_lt_sq ht h, filter_prime_eq_Ico, Set.mem_Icc]
  simp only [PrimeRecipRange, Set.mem_Icc] at hr
  exact ⟨add_le_add le_rfl hr.1, add_le_add le_rfl hr.2⟩

/-! ## Deriving a value from the recurrence

The two steps above move the bound down one at a time, so a value of `phiB` is reached by a
derivation: walk the bound down, taking the composite step where nothing happens and the prime step
where the tree branches, until every branch reaches a bound the value is known at outright. `PhiVal`
records such a derivation and `PhiVal.sound` reads the value back off it, which is what lets an
emitted certificate be checked without the checker having to reproduce the search. -/

/-- A derivation of `phiB t B = v` from the recurrence: `leaf` stops at a known value, `comp`
steps the bound past a composite, and `split` branches at a prime. -/
public inductive PhiVal : ℕ → ℕ → ℚ → Prop
  | leaf {t B : ℕ} {v : ℚ} (h : phiB t B = v) : PhiVal t B v
  | comp {t B : ℕ} {v : ℚ} (h : ¬ (B + 1).Prime) (hv : PhiVal t B v) : PhiVal t (B + 1) v
  | split {t p : ℕ} {v₁ v₂ : ℚ} (hp : p.Prime) (h₁ : PhiVal t (p - 1) v₁)
      (h₂ : PhiVal (t / p) (p - 1) v₂) : PhiVal t p (v₁ - (p : ℚ)⁻¹ * v₂)

/-- A derivation names the value it derives. -/
public theorem PhiVal.sound {t B : ℕ} {v : ℚ} (h : PhiVal t B v) : phiB t B = v := by
  induction h with
  | leaf h => exact h
  | comp h _ ih => rw [phiB_succ_not_prime h, ih]
  | split hp _ _ ih₁ ih₂ => rw [phiB_succ_prime hp, ih₁, ih₂]

/-- Nothing is left to sum below `1`. -/
public theorem phiB_zero (B : ℕ) : phiB 0 B = 0 :=
  Finset.sum_eq_zero fun n hn ↦ by
    obtain ⟨h₁, h₂, -⟩ := mem_phiSet.mp hn
    exact absurd h₂ (by omega)

/-- A derivation crosses a whole prime gap in one step. -/
public theorem PhiVal.ofRange {t B B' : ℕ} {v : ℚ} (h : B' ≤ B)
    (hno : ∀ q, B' < q → q ≤ B → ¬ q.Prime) (hv : PhiVal t B' v) : PhiVal t B v :=
  .leaf ((phiB_of_no_primes h hno).trans hv.sound)

/-- The branch that has sieved everything away. -/
public theorem PhiVal.zero (B : ℕ) : PhiVal 0 B 0 := .leaf (phiB_zero B)

/-- The branch whose bound has overtaken its height, leaving only `1`. -/
public theorem PhiVal.one {t B : ℕ} (ht : 0 < t) (h : t ≤ B) : PhiVal t B 1 :=
  .leaf (phiB_of_le ht h)

/-! ## The sieve's window is this set

A segment run's surviving bits are exactly the numbers with no prime factor at or below the base
bound, which is `phiSet` restricted to the window. Unlike the primality statement this needs no
relation between the bound and the window's height: soundness and completeness alone give it. -/

/-- A surviving bit of a completed run names a member of `phiSet`, and conversely. -/
public theorem mem_phiSet_iff_testBit {s B a W t j : ℕ}
    (hsound : Sieve.SegmentSound s B a W) (hcomplete : Sieve.SegmentComplete s B a W)
    (hj : j < W) (hle : Sieve.value (Sieve.index a + j) ≤ t) :
    Sieve.value (Sieve.index a + j) ∈ phiSet t B ↔
      (Sieve.segLoopK s (Sieve.index a) (W - 1) (Sieve.initSegK W) 1
        (Sieve.index B)).testBit j = true := by
  rw [mem_phiSet]
  have hpos : 0 < Sieve.value (Sieve.index a + j) := by rw [Sieve.value]; omega
  constructor
  · rintro ⟨-, -, hq⟩
    exact hcomplete j hj hq
  · intro hbit
    exact ⟨hle, hpos, fun q hq hqp ↦ hsound j hj (by rw [hbit]) q hq hqp⟩

/-- Once the bound reaches 3 the only survivor below 5 is `1`, so the value is `1` plus the
survivors from 5 upward, which is the range a run's windows cover between them. -/
public theorem phiB_eq_one_add_filter {t B : ℕ} (ht : 0 < t) (hB : 3 ≤ B) :
    phiB t B
      = 1 + ∑ n ∈ (Finset.Ico 5 (t + 1)).filter (fun n ↦ ∀ q ≤ B, q.Prime → ¬ q ∣ n),
          (n : ℚ)⁻¹ := by
  have hset : phiSet t B
      = insert 1 ((Finset.Ico 5 (t + 1)).filter fun n ↦ ∀ q ≤ B, q.Prime → ¬ q ∣ n) := by
    ext n
    simp only [mem_phiSet, mem_insert, mem_filter, Finset.mem_Ico, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hnt, hn0, hq⟩
      rcases Nat.lt_or_ge n 5 with hlt | hge
      · have h2 : n % 2 ≠ 0 := fun h ↦ hq 2 (by omega) Nat.prime_two (Nat.dvd_of_mod_eq_zero h)
        have h3 : n % 3 ≠ 0 := fun h ↦ hq 3 (by omega) Nat.prime_three (Nat.dvd_of_mod_eq_zero h)
        left
        omega
      · exact Or.inr ⟨⟨hge, hnt⟩, hq⟩
    · rintro (rfl | ⟨⟨h5, hnt⟩, hq⟩)
      · exact ⟨ht, one_pos, fun q _ hqp hdvd ↦ hqp.one_lt.ne' (Nat.dvd_one.mp hdvd)⟩
      · exact ⟨hnt, by omega, hq⟩
  rw [phiB, hset, Finset.sum_insert (by simp)]
  norm_num

/-- A run's scan sums the reciprocals of exactly the numbers in its range with no prime factor at
or below the bound. A branch truncated before the bound reaches 1 is answered by this, where the
sieve is stopped at `B` rather than carried to the square root. The bound must reach 3 so that the
survivors are coprime to 6 and the wheel can name them. -/
public theorem recipSum_eq_phiSum {s B lo len : ℕ} (hB : 3 ≤ B)
    (hbit : ∀ j, lo ≤ j → j < lo + len →
      (s.testBit j ↔ ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value j)) :
    recipSum s lo len 1
      = ∑ n ∈ (Finset.Ico (Sieve.value lo) (Sieve.value (lo + len))).filter
          (fun n ↦ ∀ q ≤ B, q.Prime → ¬ q ∣ n), (n : ℚ)⁻¹ :=
  recipSum_eq_filterSum_range hbit fun n _ _ hn ↦ by
    have h2 : n % 2 ≠ 0 := fun h ↦ hn 2 (by omega) Nat.prime_two (Nat.dvd_of_mod_eq_zero h)
    have h3 : n % 3 ≠ 0 := fun h ↦ hn 3 (by omega) Nat.prime_three (Nat.dvd_of_mod_eq_zero h)
    omega

/-- A run whose windows end exactly at `t` gives the value as `1` plus its own scan. -/
public theorem phiB_eq_one_add_recipSum {s B t len : ℕ} (hB : 3 ≤ B) (ht : 0 < t)
    (hbit : ∀ j, 1 ≤ j → j < 1 + len →
      (s.testBit j ↔ ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value j))
    (hend : Sieve.value (1 + len) = t + 1) :
    phiB t B = 1 + recipSum s 1 len 1 := by
  have h5 : Sieve.value 1 = 5 := by rw [Sieve.value]
  rw [phiB_eq_one_add_filter ht hB, recipSum_eq_phiSum hB hbit, hend, h5]

/-- The same run as a rational enclosure, which is the shape an emitted leaf would carry: the
total and the count of contributing positions are two literals over one scale. -/
public theorem phiB_mem_Icc_of_run {s S B t len A C : ℕ} (hB : 3 ≤ B) (ht : 0 < t)
    (hS : Nat.blt 0 S = true)
    (hbit : ∀ j, 1 ≤ j → j < 1 + len →
      (s.testBit j ↔ ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value j))
    (hend : Sieve.value (1 + len) = t + 1)
    (hA : sumB (recipAtK s S) 1 len 1 = A) (hC : sumB (bitAtK s) 1 len 1 = C) :
    phiB t B ∈ Set.Icc (1 + (A : ℚ) / S) (1 + ((A : ℚ) + (C : ℚ)) / S) := by
  rw [Nat.blt_eq] at hS
  rw [phiB_eq_one_add_recipSum hB ht hbit hend, Set.mem_Icc]
  have hmem := recipSum_mem_Icc (S := S) s 1 len 1 (by omega)
  rw [hA, hC] at hmem
  exact ⟨add_le_add le_rfl hmem.1, add_le_add le_rfl hmem.2⟩

end PrimeCert
