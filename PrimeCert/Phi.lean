/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.PrimeHarmonic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
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

/-- The survivors whose least prime factor is `p` are `p` times the survivors below `t / p` that
have no factor under `p`. Classifying by least prime factor is what turns the sieved sum into the
identity's one-step expansion. -/
theorem phiSet_filter_minFac {t B p : ℕ} (hp : p.Prime) (hB : B < p) :
    ((phiSet t B).filter fun n ↦ n.minFac = p)
      = (phiSet (t / p) (p - 1)).image (fun m ↦ p * m) := by
  have hp0 : 0 < p := hp.pos
  ext n
  simp only [mem_filter, mem_phiSet, mem_image]
  constructor
  · rintro ⟨⟨hnt, hn0, hq⟩, hmin⟩
    have hdvd : p ∣ n := hmin ▸ Nat.minFac_dvd n
    obtain ⟨m, rfl⟩ := hdvd
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at hn0
      · exact h
    refine ⟨m, ⟨?_, hm0, ?_⟩, rfl⟩
    · exact (Nat.le_div_iff_mul_le hp0).mpr (by rw [Nat.mul_comm] at hnt; exact hnt)
    · intro q hq' hqp hqm
      have : (p * m).minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le (hqm.mul_left p)
      omega
  · rintro ⟨m, ⟨hmt, hm0, hq⟩, rfl⟩
    have hle : p * m ≤ t := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_of_le_div p m t hmt
    have hne : p * m ≠ 1 := by
      have h2 : 2 * 1 ≤ p * m := Nat.mul_le_mul hp.two_le hm0
      omega
    have hmin : (p * m).minFac = p := by
      have hup : (p * m).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le ⟨m, rfl⟩
      by_contra hneq
      have hlt : (p * m).minFac < p := lt_of_le_of_ne hup hneq
      have hpr : (p * m).minFac.Prime := Nat.minFac_prime hne
      rcases (Nat.Prime.dvd_mul hpr).mp (Nat.minFac_dvd (p * m)) with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hpr hp).mp h
        omega
      · exact hq _ (by omega) hpr h
    refine ⟨⟨hle, Nat.mul_pos hp0 hm0, ?_⟩, hmin⟩
    intro q hq' hqp hqd
    have : (p * m).minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le hqd
    omega

/-- **The expansion.** Every survivor above `1` has a least prime factor, which lies above `B` and
at or below `t`, and the survivors sharing one are `p` times the survivors below `t / p` with
nothing under `p`. So the sieved sum is `1` plus one term per prime in that range, each a copy of
the same function lower down. Taking `B` to the square root leaves only primes with
`phiB (t / p) (p - 1) = 1`, which is the plain sum of reciprocals of primes. -/
public theorem phiB_eq_one_add_sum {t B : ℕ} (ht : 0 < t) :
    phiB t B = 1 + ∑ p ∈ (Finset.Icc (B + 1) t).filter Nat.Prime,
      (p : ℚ)⁻¹ * phiB (t / p) (p - 1) := by
  have h1mem : (1 : ℕ) ∈ phiSet t B :=
    mem_phiSet.mpr ⟨ht, one_pos, fun q _ hqp hdvd ↦ hqp.one_lt.ne' (Nat.dvd_one.mp hdvd)⟩
  have hsplit : phiSet t B = insert 1 ((phiSet t B).filter fun n ↦ n ≠ 1) := by
    ext n
    simp only [mem_insert, mem_filter]
    constructor
    · intro h
      rcases eq_or_ne n 1 with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr ⟨h, hne⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact h1mem
      · exact h
  have hnot : (1 : ℕ) ∉ (phiSet t B).filter fun n ↦ n ≠ 1 := by simp
  have hmaps : ∀ n ∈ (phiSet t B).filter (fun n ↦ n ≠ 1),
      n.minFac ∈ (Finset.Icc (B + 1) t).filter Nat.Prime := by
    intro n hn
    simp only [mem_filter, mem_phiSet] at hn
    obtain ⟨⟨hnt, hn0, hq⟩, hne⟩ := hn
    have hpr : n.minFac.Prime := Nat.minFac_prime hne
    simp only [mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, (Nat.minFac_le hn0).trans hnt⟩, hpr⟩
    by_contra hc
    exact hq n.minFac (by omega) hpr (Nat.minFac_dvd n)
  have hclass : ∀ p ∈ (Finset.Icc (B + 1) t).filter Nat.Prime,
      ∑ n ∈ ((phiSet t B).filter fun n ↦ n ≠ 1).filter (fun n ↦ n.minFac = p), ((n : ℚ))⁻¹
        = (p : ℚ)⁻¹ * phiB (t / p) (p - 1) := by
    intro p hp
    simp only [mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hBp, hpt⟩, hpr⟩ := hp
    have heq : ((phiSet t B).filter fun n ↦ n ≠ 1).filter (fun n ↦ n.minFac = p)
        = (phiSet t B).filter (fun n ↦ n.minFac = p) := by
      ext n
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨h, -⟩, hm⟩
        exact ⟨h, hm⟩
      · rintro ⟨h, hm⟩
        refine ⟨⟨h, ?_⟩, hm⟩
        rintro rfl
        rw [Nat.minFac_one] at hm
        have := hpr.two_le
        omega
    rw [heq, phiSet_filter_minFac hpr (by omega),
      Finset.sum_image (fun a _ b _ hab ↦ Nat.eq_of_mul_eq_mul_left hpr.pos hab), phiB,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    push_cast
    rw [mul_inv]
  rw [phiB, hsplit, Finset.sum_insert hnot,
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun n ↦ ((n : ℕ) : ℚ)⁻¹),
    Finset.sum_congr rfl hclass]
  norm_num

/-- With the bound past the square root every branch of the expansion is already finished, so it
collapses to the plain sum over primes. `phiB_of_lt_sq` reaches the same value by counting
survivors instead of expanding, so the two are a check on each other. -/
public theorem phiB_eq_one_add_primeSum {t B : ℕ} (ht : 0 < t) (hB : t < (B + 1) * (B + 1)) :
    phiB t B = 1 + ∑ p ∈ (Finset.Icc (B + 1) t).filter Nat.Prime, (p : ℚ)⁻¹ := by
  rw [phiB_eq_one_add_sum ht]
  refine congrArg (1 + ·) (Finset.sum_congr rfl fun p hp ↦ ?_)
  simp only [mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hBp, hpt⟩, hpr⟩ := hp
  have hp0 : 0 < p := hpr.pos
  have hdiv : t / p < p := by
    refine (Nat.div_lt_iff_lt_mul hp0).mpr ?_
    calc t < (B + 1) * (B + 1) := hB
      _ ≤ p * p := Nat.mul_le_mul hBp hBp
  rw [phiB_of_le (Nat.div_pos hpt hp0) (by omega), mul_one]

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

/-! ### The same derivation, carrying enclosures

An emitted leaf is an interval, not a rational, so a derivation that can actually be built from a
sweep has to carry intervals. The branch subtracts, so its bounds cross: the lower bound of a
split takes the lower bound of the left branch against the UPPER bound of the right. -/

/-- An enclosure of `phiB t B` derived by the recurrence. This is the form a certificate takes,
since every leaf a sweep answers is an interval. -/
public inductive PhiEnc : ℕ → ℕ → ℚ → ℚ → Prop
  | leaf {t B : ℕ} {lo hi : ℚ} (h : phiB t B ∈ Set.Icc lo hi) : PhiEnc t B lo hi
  | comp {t B : ℕ} {lo hi : ℚ} (h : ¬ (B + 1).Prime) (hv : PhiEnc t B lo hi) :
      PhiEnc t (B + 1) lo hi
  | split {t p : ℕ} {lo₁ hi₁ lo₂ hi₂ : ℚ} (hp : p.Prime)
      (h₁ : PhiEnc t (p - 1) lo₁ hi₁) (h₂ : PhiEnc (t / p) (p - 1) lo₂ hi₂) :
      PhiEnc t p (lo₁ - (p : ℚ)⁻¹ * hi₂) (hi₁ - (p : ℚ)⁻¹ * lo₂)

/-- A derivation encloses what it claims to. -/
public theorem PhiEnc.sound {t B : ℕ} {lo hi : ℚ} (h : PhiEnc t B lo hi) :
    phiB t B ∈ Set.Icc lo hi := by
  induction h with
  | leaf h => exact h
  | comp h _ ih => rwa [phiB_succ_not_prime h]
  | @split t p lo₁ hi₁ lo₂ hi₂ hp h₁ h₂ ih₁ ih₂ =>
    rw [Set.mem_Icc] at ih₁ ih₂ ⊢
    rw [phiB_succ_prime hp]
    have hppos : (0 : ℚ) < (p : ℚ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.pos)
    have hup := mul_le_mul_of_nonneg_left ih₂.2 hppos.le
    have hdown := mul_le_mul_of_nonneg_left ih₂.1 hppos.le
    exact ⟨by linarith [ih₁.1], by linarith [ih₁.2]⟩

/-- An exactly known value is the interval of zero width. -/
public theorem PhiEnc.ofEq {t B : ℕ} {v : ℚ} (h : phiB t B = v) : PhiEnc t B v v :=
  .leaf (by rw [h]; exact ⟨le_rfl, le_rfl⟩)

/-- A derivation crosses a whole prime gap in one step. -/
public theorem PhiEnc.ofRange {t B B' : ℕ} {lo hi : ℚ} (h : B' ≤ B)
    (hno : ∀ q, B' < q → q ≤ B → ¬ q.Prime) (hv : PhiEnc t B' lo hi) : PhiEnc t B lo hi :=
  .leaf (by rw [phiB_of_no_primes h hno]; exact hv.sound)

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

/-! ## The harmonic leaf at scale

A branch that reaches bound `1` has nothing sieved out, so its value is the plain harmonic sum.
Folding the rounded-down reciprocals at scale `S` encloses it with one unit of slack per term. -/

/-- The reciprocal of `n` at scale `S`, rounded down: the summand of the plain harmonic fold. -/
@[expose] public def recipPlain (S n : ℕ) : ℕ := S / n

theorem sumB_succ' (f : ℕ → ℕ) (start len step : ℕ) :
    sumB f start (len + 1) step = f ((len.mul step).add start) + sumB f start len step := rfl

/-- One term: the rounded reciprocal sits under the true one and within one unit of it. -/
theorem recipPlain_bounds {S k : ℕ} (hk : 0 < k) :
    ((recipPlain S k : ℕ) : ℚ) ≤ (S : ℚ) * (k : ℚ)⁻¹ ∧
      (S : ℚ) * (k : ℚ)⁻¹ ≤ ((recipPlain S k : ℕ) : ℚ) + 1 := by
  have hkq : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have h : S < (S / k + 1) * k := by
    have h1 := Nat.div_add_mod S k
    have h2 := Nat.mod_lt S hk
    nlinarith [h1, h2]
  constructor
  · rw [recipPlain, ← div_eq_mul_inv, le_div_iff₀ hkq]
    exact_mod_cast Nat.div_mul_le_self S k
  · rw [recipPlain, ← div_eq_mul_inv, div_le_iff₀ hkq]
    exact_mod_cast h.le

/-- The fold of the rounded reciprocals over `1 … t` encloses the harmonic sum of that range,
with one unit of slack per term. -/
theorem sumB_recipPlain_bounds (S t : ℕ) :
    ((sumB (recipPlain S) 1 t 1 : ℕ) : ℚ) ≤ (S : ℚ) * ∑ n ∈ Finset.Icc 1 t, (n : ℚ)⁻¹ ∧
      (S : ℚ) * ∑ n ∈ Finset.Icc 1 t, (n : ℚ)⁻¹
        ≤ ((sumB (recipPlain S) 1 t 1 : ℕ) : ℚ) + t := by
  induction t with
  | zero => simp
  | succ m ih =>
    obtain ⟨hlo, hhi⟩ := ih
    obtain ⟨tlo, thi⟩ := recipPlain_bounds (S := S) (k := m + 1) (by omega)
    have hidx : (m.mul 1).add 1 = m + 1 := by
      change m * 1 + 1 = m + 1
      omega
    rw [Finset.sum_Icc_succ_top (by omega), sumB_succ', hidx]
    push_cast at tlo thi ⊢
    rw [mul_add]
    constructor
    · linarith
    · linarith

/-- The harmonic leaf at scale: the value of a branch whose bound has reached `1`, enclosed by the
fold of the rounded reciprocals with `t` units of slack. -/
public theorem phiB_one_mem_Icc_of_fold {t S A C : ℕ} (hS : Nat.blt 0 S = true)
    (hA : sumB (recipPlain S) 1 t 1 = A) (hC : Nat.beq t C = true) :
    phiB t 1 ∈ Set.Icc ((A : ℚ) / S) (((A : ℚ) + (C : ℚ)) / S) := by
  rw [Nat.blt_eq] at hS
  rw [Nat.beq_eq] at hC
  subst hA
  subst hC
  have hSq : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS
  have hsum : phiB t 1 = ∑ n ∈ Finset.Icc 1 t, (n : ℚ)⁻¹ := by
    rw [phiB_one]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext n
    simp only [mem_filter, mem_range, Finset.mem_Icc]
    omega
  obtain ⟨hlo, hhi⟩ := sumB_recipPlain_bounds S t
  rw [hsum, Set.mem_Icc]
  constructor
  · rw [div_le_iff₀ hSq, mul_comm]
    exact hlo
  · rw [le_div_iff₀ hSq, mul_comm]
    exact hhi

/-! ## Ranges of the sieved sum, which a sweep accumulates

A leaf is answered at a point of a sweep rather than by a run of its own, so what it needs is a
prefix of the sieved sum: windows enclosed one at a time and added along the sweep, with each leaf
reading the total where its own height falls. This mirrors `PrimeRecipRange` and its addition,
with the sieve stopped at `B` instead of carried to the square root. -/

/-- The sum of the reciprocals of the numbers in `a … b - 1` with no prime factor at or below `B`
lies in the interval of width `C / S` above `A / S`. -/
@[expose] public noncomputable def SievedRecipRange (a b B A C S : ℕ) : Prop :=
  ∑ n ∈ (Finset.Ico a b).filter (fun n ↦ ∀ q ≤ B, q.Prime → ¬ q ∣ n), (n : ℚ)⁻¹ ∈
    Set.Icc ((A : ℚ) / S) (((A : ℚ) + (C : ℚ)) / S)

/-- A scan of one window encloses the sieved sum over the numbers it covers. -/
public theorem sievedRecipRange_of {s S B lo len A C : ℕ} (hB : 3 ≤ B)
    (hS : Nat.blt 0 S = true)
    (hbit : ∀ j, lo ≤ j → j < lo + len →
      (s.testBit j ↔ ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value j))
    (hA : sumB (recipAtK s S) lo len 1 = A) (hC : sumB (bitAtK s) lo len 1 = C) :
    SievedRecipRange (Sieve.value lo) (Sieve.value (lo + len)) B A C S := by
  rw [Nat.blt_eq] at hS
  have hmem := recipSum_mem_Icc (S := S) s lo len 1 (by omega)
  rw [recipSum_eq_phiSum hB hbit, hA, hC] at hmem
  exact hmem

/-- Two neighbouring ranges add, with the two totals and the two counts added as literals. This is
the step a sweep takes between leaves. -/
public theorem sievedRecipRange_add {a b c B A₁ C₁ A₂ C₂ A C S : ℕ}
    (hab : Nat.ble a b = true) (hbc : Nat.ble b c = true)
    (h₁ : SievedRecipRange a b B A₁ C₁ S) (h₂ : SievedRecipRange b c B A₂ C₂ S)
    (hA : Nat.beq (Nat.add A₁ A₂) A = true) (hC : Nat.beq (Nat.add C₁ C₂) C = true) :
    SievedRecipRange a c B A C S := by
  rw [Nat.beq_eq] at hA hC
  rw [Nat.ble_eq] at hab hbc
  rw [SievedRecipRange, Finset.sum_filter] at h₁ h₂ ⊢
  rw [← Finset.sum_Ico_consecutive _ hab hbc]
  obtain ⟨hlo₁, hhi₁⟩ := h₁
  obtain ⟨hlo₂, hhi₂⟩ := h₂
  subst hA
  subst hC
  simp only [Nat.add_eq]
  push_cast
  simp only [add_div] at hhi₁ hhi₂ ⊢
  exact ⟨by linarith, by linarith⟩

/-- One sieved segment as an enclosure of the sieved sum over the numbers it covers. The segment
command already emits these hypotheses, since soundness and completeness are stated against this
very property. Unlike the prime version this needs no bound tying the window's top to `B ^ 2`:
nothing has to be upgraded to primality, so a segment far above the square root still answers. -/
public theorem sievedRecipRange_segment {B a W S g A C : ℕ}
    (ha : a % 6 = 1 ∨ a % 6 = 5) (hB3 : 3 ≤ B) (hS : Nat.blt 0 S = true)
    (hsound : ∀ j < W, g.testBit j = true →
      ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value (Sieve.index a + j))
    (hcomplete : ∀ j < W,
      (∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value (Sieve.index a + j)) → g.testBit j = true)
    (hA : sumB (recipAtW g (Sieve.index a) S) 0 W 1 = A)
    (hC : sumB (bitAtW g) 0 W 1 = C) :
    SievedRecipRange a (Sieve.value (Sieve.index a + W)) B A C S := by
  have hlo : Sieve.value (Sieve.index a) = a := Sieve.value_index ha
  have hbit : ∀ j, Sieve.index a ≤ j → j < Sieve.index a + W →
      ((Nat.shiftLeft g (Sieve.index a)).testBit j ↔
        ∀ q ≤ B, q.Prime → ¬ q ∣ Sieve.value j) := by
    intro j h1 h2
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1
    rw [testBit_shiftLeft_add]
    exact ⟨fun h ↦ hsound k (by omega) h, fun h ↦ hcomplete k (by omega) h⟩
  have hA' : sumB (recipAtK (Nat.shiftLeft g (Sieve.index a)) S) (Sieve.index a) W 1 = A := by
    rw [recip_shift]
    exact hA
  have hC' : sumB (bitAtK (Nat.shiftLeft g (Sieve.index a))) (Sieve.index a) W 1 = C := by
    rw [bit_shift]
    exact hC
  have h := sievedRecipRange_of hB3 hS hbit hA' hC'
  rwa [hlo] at h

/-- Everything a segment run's output supplies for a sieved leaf, in one application: the base
sieve, the equation the segment command emits, the numeric side conditions as `Bool` literals, and
the two folds over the segment literal. -/
public theorem sievedRecipRange_of_segRun {s B a W S g A C lo next : ℕ} (hs : Sieve.IsSieve B s)
    (ha : Nat.mod a 6 = 1 ∨ Nat.mod a 6 = 5) (hB6 : Nat.mod B 6 = 1 ∨ Nat.mod B 6 = 5)
    (hW : Nat.blt (W - 1) (2 ^ 32) = true)
    (hB3 : Nat.ble 3 B = true) (h7B : Nat.ble (7 * B) a = true)
    (hS : Nat.blt 0 S = true)
    (hlo : Nat.beq (Sieve.index a) lo = true)
    (htv : Nat.beq (Sieve.value (lo + W)) next = true)
    (hseg : Sieve.segRun s a W B = g)
    (hA : sumB (recipAtW g lo S) 0 W 1 = A)
    (hC : sumB (bitAtW g) 0 W 1 = C) :
    SievedRecipRange a next B A C S := by
  rw [Nat.beq_eq] at hlo htv
  subst hlo
  subst htv
  rw [Nat.ble_eq] at hB3 h7B
  rw [Nat.blt_eq] at hW
  rw [Sieve.segRun_eq] at hseg
  have hsound' := Sieve.segmentSound_of hs ha hW (by omega) h7B
  have hcomplete' := Sieve.segmentComplete_of hs hB6 hW h7B
  rw [Sieve.SegmentSound] at hsound'
  rw [Sieve.SegmentComplete] at hcomplete'
  rw [hseg] at hsound' hcomplete'
  exact sievedRecipRange_segment ha hB3 hS (fun j hj h ↦ hsound' j hj h) hcomplete' hA hC

/-- Nothing at or below the bound survives it, since such a number is divisible by itself. A
leaf's range therefore starts at `B + 1`, and this supplies the stretch beneath it. -/
public theorem sievedRecipRange_below {b B S : ℕ} (hb : b ≤ B + 1) :
    SievedRecipRange 5 b B 0 0 S := by
  have hset : (Finset.Ico 5 b).filter (fun n ↦ ∀ q ≤ B, q.Prime → ¬ q ∣ n) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro n hn
    simp only [Finset.mem_Ico] at hn
    intro hsv
    have hn1 : n ≠ 1 := by omega
    exact hsv n.minFac (le_trans (Nat.minFac_le (by omega)) (by omega)) (Nat.minFac_prime hn1)
      (Nat.minFac_dvd n)
  rw [SievedRecipRange, hset]
  simp

/-- Below the square of the bound a survivor is prime, so a proved range of primes serves as a
range of survivors. A leaf's range splits here: the part under `B ^ 2` reuses the enclosures the
prime run already produces, and the part above it comes from `sievedRecipRange_of_segRun`. -/
public theorem sievedRecipRange_of_primeRecipRange {a b B A C S : ℕ} (hB1 : 1 ≤ B) (hBa : B < a)
    (hb : b ≤ B * B) (h : PrimeRecipRange a b A C S) : SievedRecipRange a b B A C S := by
  have hset : (Finset.Ico a b).filter Nat.Prime
      = (Finset.Ico a b).filter (fun n ↦ ∀ q ≤ B, q.Prime → ¬ q ∣ n) := by
    ext n
    simp only [mem_filter, Finset.mem_Ico]
    refine and_congr_right fun hn ↦ ⟨fun hpr q hq hqp hqd ↦ ?_, fun hsv ↦ ?_⟩
    · have := (Nat.prime_dvd_prime_iff_eq hqp hpr).mp hqd
      omega
    · by_contra hnp
      have hn1 : n ≠ 1 := by omega
      have hmf : n.minFac.Prime := Nat.minFac_prime hn1
      have hsq : n.minFac * n.minFac ≤ n := by
        have h2 : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
        rwa [pow_two] at h2
      have hlt : n.minFac ≤ B := by
        by_contra hc
        have hc' : B + 1 ≤ n.minFac := by omega
        have h1 : (B + 1) * (B + 1) ≤ n.minFac * n.minFac := Nat.mul_le_mul hc' hc'
        have h2 : (B + 1) * (B + 1) = B * B + 2 * B + 1 := by ring
        omega
      exact hsv n.minFac hlt hmf (Nat.minFac_dvd n)
  rw [SievedRecipRange, ← hset]
  exact h

/-- The primes above `B` and at most `N` are what two runs of the base sieve differ by. -/
theorem primeSum_Ico_eq_sub {N B : ℕ} (h : B ≤ N) :
    ∑ p ∈ (Finset.Ico (B + 1) (N + 1)).filter Nat.Prime, (p : ℚ)⁻¹
      = (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (p : ℚ)⁻¹)
        - ∑ p ∈ (Finset.range (B + 1)).filter Nat.Prime, (p : ℚ)⁻¹ := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.range_eq_Ico,
    Finset.range_eq_Ico, eq_sub_iff_add_eq, add_comm]
  exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)

/-- The stretch of survivors between the bound and its square, taken as the difference of two
enclosures the base run already proves. The lower end subtracts the wider of the two intervals,
so both subtractions are stated as additions. -/
public theorem sievedRecipRange_of_two_icc {N B A₁ C₁ A₂ C₂ L C S : ℕ}
    (hB1 : 1 ≤ B) (hN : B ≤ N) (hsq : N + 1 ≤ B * B)
    (h₁ : PrimeRecipIcc N A₁ C₁ S) (h₂ : PrimeRecipIcc B A₂ C₂ S)
    (hL : Nat.beq (L + A₂ + C₂) A₁ = true)
    (hU : Nat.beq (L + C + A₂) (A₁ + C₁) = true) :
    SievedRecipRange (B + 1) (N + 1) B L C S := by
  rw [Nat.beq_eq] at hL hU
  refine sievedRecipRange_of_primeRecipRange hB1 (by omega) hsq ?_
  rw [PrimeRecipIcc, Set.mem_Icc] at h₁ h₂
  rw [PrimeRecipRange, Set.mem_Icc, primeSum_Ico_eq_sub hN]
  have e₁ : ((L : ℚ) + A₂ + C₂) / S = (A₁ : ℚ) / S := by
    rw [show ((L : ℚ) + A₂ + C₂) = ((L + A₂ + C₂ : ℕ) : ℚ) by push_cast; ring, hL]
  have e₂ : ((L : ℚ) + C + A₂) / S = ((A₁ : ℚ) + C₁) / S := by
    rw [show ((L : ℚ) + C + A₂) = ((L + C + A₂ : ℕ) : ℚ) by push_cast; ring, hU]
    push_cast
    ring
  simp only [add_div] at h₁ h₂ e₁ e₂ ⊢
  constructor
  · linarith [h₁.1, h₂.2]
  · linarith [h₁.2, h₂.1]

/-- A range may be carried up over a stretch holding no survivor, which is how a leaf whose height
falls between two wheel values is answered: the numbers in between are divisible by 2 or by 3. -/
public theorem sievedRecipRange_extend {a b b' B A C S : ℕ} (hb : b ≤ b')
    (hno : ∀ n, b ≤ n → n < b' → ∃ q, q ≤ B ∧ q.Prime ∧ q ∣ n)
    (h : SievedRecipRange a b B A C S) : SievedRecipRange a b' B A C S := by
  have hset : (Finset.Ico a b').filter (fun n ↦ ∀ q ≤ B, q.Prime → ¬ q ∣ n)
      = (Finset.Ico a b).filter (fun n ↦ ∀ q ≤ B, q.Prime → ¬ q ∣ n) := by
    ext n
    simp only [mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hna, hnb'⟩, hsv⟩
      refine ⟨⟨hna, ?_⟩, hsv⟩
      by_contra hc
      obtain ⟨q, hq, hqp, hqd⟩ := hno n (by omega) hnb'
      exact hsv q hq hqp hqd
    · rintro ⟨⟨hna, hnb⟩, hsv⟩
      exact ⟨⟨hna, by omega⟩, hsv⟩
  rw [SievedRecipRange, hset]
  exact h

/-- The value read off an enclosure of its whole range. The sum runs from 5, so the surviving `1`
is added back here. -/
public theorem phiB_mem_Icc_of_range {t B A C S : ℕ} (ht : 0 < t) (hB : 3 ≤ B)
    (hr : SievedRecipRange 5 (t + 1) B A C S) :
    phiB t B ∈ Set.Icc (1 + (A : ℚ) / S) (1 + ((A : ℚ) + (C : ℚ)) / S) := by
  rw [phiB_eq_one_add_filter ht hB, Set.mem_Icc]
  simp only [SievedRecipRange, Set.mem_Icc] at hr
  exact ⟨add_le_add le_rfl hr.1, add_le_add le_rfl hr.2⟩

/-- A leaf answered by a sweep: the range enclosure of its whole height becomes a derivation, so
a truncated branch and an expanded one carry the same kind of object. -/
public theorem PhiEnc.ofSweep {t B A C S : ℕ} (ht : 0 < t) (hB : 3 ≤ B)
    (hr : SievedRecipRange 5 (t + 1) B A C S) :
    PhiEnc t B (1 + (A : ℚ) / S) (1 + ((A : ℚ) + (C : ℚ)) / S) :=
  .leaf (phiB_mem_Icc_of_range ht hB hr)

/-- The sweep leaf in the same scaled form as the branch, so a derivation is integer literals
throughout. The surviving `1` becomes the scale itself. -/
public theorem phiB_mem_Icc_of_range_scaled {t B A C S L U : ℕ} (ht : 0 < t) (hB : 3 ≤ B)
    (hS : Nat.blt 0 S = true) (hr : SievedRecipRange 5 (t + 1) B A C S)
    (hL : Nat.beq (S + A) L = true) (hU : Nat.beq (S + A + C) U = true) :
    phiB t B ∈ Set.Icc ((L : ℚ) / S) ((U : ℚ) / S) := by
  rw [Nat.blt_eq] at hS
  rw [Nat.beq_eq] at hL hU
  subst hL
  subst hU
  have hSne : (S : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS
    exact ne_of_gt this
  have h := phiB_mem_Icc_of_range ht hB hr
  push_cast
  rw [show ((S : ℚ) + A) / S = 1 + (A : ℚ) / S by field_simp,
    show ((S : ℚ) + A + C) / S = 1 + ((A : ℚ) + C) / S by field_simp; ring]
  exact h

/-- Crossing a prime gap keeps the enclosure, so a derivation stays on the scale throughout. -/
public theorem phiB_mem_Icc_of_no_primes {t B B' L U S : ℕ} (h : B' ≤ B)
    (hno : ∀ q, B' < q → q ≤ B → ¬ q.Prime)
    (hv : phiB t B' ∈ Set.Icc ((L : ℚ) / S) ((U : ℚ) / S)) :
    phiB t B ∈ Set.Icc ((L : ℚ) / S) ((U : ℚ) / S) := by
  rw [phiB_of_no_primes h hno]
  exact hv

/-- A branch sieved away, on the scale. -/
public theorem phiB_zero_mem_Icc (B S : ℕ) :
    phiB 0 B ∈ Set.Icc ((0 : ℚ) / S) ((0 : ℚ) / S) := by
  rw [phiB_zero]
  simp

/-- A branch whose bound has overtaken its height, on the scale: the value is the scale itself. -/
public theorem phiB_one_mem_Icc {t B S : ℕ} (ht : 0 < t) (h : t ≤ B) (hS : Nat.blt 0 S = true) :
    phiB t B ∈ Set.Icc ((S : ℚ) / S) ((S : ℚ) / S) := by
  rw [Nat.blt_eq] at hS
  have hSne : (S : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS
    exact ne_of_gt this
  rw [phiB_of_le ht h, div_self hSne]
  exact ⟨le_rfl, le_rfl⟩

/-- The branch, with both ends as scaled integer literals rather than rationals, which is how the
rest of the project states an enclosure. The division by `p` is supplied by the emitter as two
quotients: `Qhi` sits above the right branch's upper end over `p`, `Qlo` below its lower end, and
the two subtractions are stated as additions so nothing truncates. -/
public theorem phiB_mem_Icc_split {t p S L₁ U₁ L₂ U₂ Qlo Qhi L U : ℕ} (hp : p.Prime)
    (hS : Nat.blt 0 S = true)
    (h₁ : phiB t (p - 1) ∈ Set.Icc ((L₁ : ℚ) / S) ((U₁ : ℚ) / S))
    (h₂ : phiB (t / p) (p - 1) ∈ Set.Icc ((L₂ : ℚ) / S) ((U₂ : ℚ) / S))
    (hhi : Nat.ble U₂ (Qhi * p) = true) (hlo : Nat.ble (Qlo * p) L₂ = true)
    (hL : Nat.beq (L + Qhi) L₁ = true) (hU : Nat.beq (U + Qlo) U₁ = true) :
    phiB t p ∈ Set.Icc ((L : ℚ) / S) ((U : ℚ) / S) := by
  rw [Nat.blt_eq] at hS
  rw [Nat.ble_eq] at hhi hlo
  rw [Nat.beq_eq] at hL hU
  subst hL
  subst hU
  rw [Set.mem_Icc] at h₁ h₂ ⊢
  rw [phiB_succ_prime hp]
  have hSpos : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS
  have hppos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hpinv : (0 : ℚ) < (p : ℚ)⁻¹ := inv_pos.mpr hppos
  have hhi' : (U₂ : ℚ) ≤ (Qhi : ℚ) * p := by exact_mod_cast hhi
  have hlo' : (Qlo : ℚ) * p ≤ (L₂ : ℚ) := by exact_mod_cast hlo
  have hSinv : (0 : ℚ) ≤ ((S : ℚ))⁻¹ := (inv_pos.mpr hSpos).le
  have g1 : (p : ℚ)⁻¹ * (U₂ : ℚ) ≤ (Qhi : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hhi' hpinv.le
    rwa [show (p : ℚ)⁻¹ * ((Qhi : ℚ) * p) = (Qhi : ℚ) by field_simp] at h
  have g2 : (Qlo : ℚ) ≤ (p : ℚ)⁻¹ * (L₂ : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hlo' hpinv.le
    rwa [show (p : ℚ)⁻¹ * ((Qlo : ℚ) * p) = (Qlo : ℚ) by field_simp] at h
  have fhi : (p : ℚ)⁻¹ * ((U₂ : ℚ) / S) ≤ (Qhi : ℚ) / S := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right g1 hSinv
  have flo : (Qlo : ℚ) / S ≤ (p : ℚ)⁻¹ * ((L₂ : ℚ) / S) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right g2 hSinv
  have fup := mul_le_mul_of_nonneg_left h₂.2 hpinv.le
  have fdn := mul_le_mul_of_nonneg_left h₂.1 hpinv.le
  push_cast at h₁ ⊢
  simp only [add_div] at h₁
  exact ⟨by linarith [h₁.1], by linarith [h₁.2]⟩

/-! ## One emitted node

An expansion is emitted node by node, so the statement a node carries is named, in the shape the
rest of the project uses: scaled integer ends over one scale. -/

/-- `phiB t B` lies in the interval whose ends are `lo / S` and `hi / S`. -/
@[expose] public noncomputable def PhiEnclosure (t B lo hi S : ℕ) : Prop :=
  phiB t B ∈ Set.Icc ((lo : ℚ) / S) ((hi : ℚ) / S)

/-- A branch sieved away. -/
public theorem phiEnclosure_zero (B S : ℕ) : PhiEnclosure 0 B 0 0 S :=
  phiB_zero_mem_Icc B S

/-- A branch whose bound has overtaken its height: the value is the scale itself. -/
public theorem phiEnclosure_one {t B S : ℕ} (ht : 0 < t) (h : t ≤ B)
    (hS : Nat.blt 0 S = true) : PhiEnclosure t B S S S :=
  phiB_one_mem_Icc ht h hS

/-- The branch whose bound has overtaken its height, with both conditions as `Bool` literals. -/
public theorem phiEnclosure_one_of_ble {t B S : ℕ} (ht : Nat.blt 0 t = true)
    (h : Nat.ble t B = true) (hS : Nat.blt 0 S = true) : PhiEnclosure t B S S S := by
  rw [Nat.blt_eq] at ht
  rw [Nat.ble_eq] at h
  exact phiEnclosure_one ht h hS

/-- Stepping the bound across a stretch with no prime in it. -/
public theorem phiEnclosure_of_no_primes {t B B' lo hi S : ℕ} (h : B' ≤ B)
    (hno : ∀ q, B' < q → q ≤ B → ¬ q.Prime) (hv : PhiEnclosure t B' lo hi S) :
    PhiEnclosure t B lo hi S :=
  phiB_mem_Icc_of_no_primes h hno hv

/-- The branch at a prime, both ends scaled integers. -/
public theorem phiEnclosure_split {t p S L₁ U₁ L₂ U₂ Qlo Qhi L U : ℕ} (hp : p.Prime)
    (hS : Nat.blt 0 S = true)
    (h₁ : PhiEnclosure t (p - 1) L₁ U₁ S) (h₂ : PhiEnclosure (t / p) (p - 1) L₂ U₂ S)
    (hhi : Nat.ble U₂ (Qhi * p) = true) (hlo : Nat.ble (Qlo * p) L₂ = true)
    (hL : Nat.beq (L + Qhi) L₁ = true) (hU : Nat.beq (U + Qlo) U₁ = true) :
    PhiEnclosure t p L U S :=
  phiB_mem_Icc_split hp hS h₁ h₂ hhi hlo hL hU

/-- The branch at a prime, with the primality itself a `Bool` literal the kernel checks: a number
at least 2 whose least factor is itself. This is the form an emitter can produce. -/
public theorem phiEnclosure_split_of_minFac {t p S L₁ U₁ L₂ U₂ Qlo Qhi L U : ℕ}
    (hp2 : Nat.ble 2 p = true) (hpm : Nat.beq (Nat.minFac p) p = true)
    (hS : Nat.blt 0 S = true)
    (h₁ : PhiEnclosure t (p - 1) L₁ U₁ S) (h₂ : PhiEnclosure (t / p) (p - 1) L₂ U₂ S)
    (hhi : Nat.ble U₂ (Qhi * p) = true) (hlo : Nat.ble (Qlo * p) L₂ = true)
    (hL : Nat.beq (L + Qhi) L₁ = true) (hU : Nat.beq (U + Qlo) U₁ = true) :
    PhiEnclosure t p L U S := by
  rw [Nat.ble_eq] at hp2
  rw [Nat.beq_eq] at hpm
  exact phiEnclosure_split ((Nat.prime_def_minFac).mpr ⟨hp2, hpm⟩) hS h₁ h₂ hhi hlo hL hU

/-- Stepping the bound past one composite, with the compositeness a `Bool` literal: a number
whose least factor is smaller than itself. -/
public theorem phiEnclosure_step_of_minFac {t B lo hi S : ℕ}
    (hBm : Nat.blt (Nat.minFac (B + 1)) (B + 1) = true)
    (hv : PhiEnclosure t B lo hi S) : PhiEnclosure t (B + 1) lo hi S := by
  rw [PhiEnclosure, phiB_succ_not_prime]
  · exact hv
  · rw [Nat.blt_eq] at hBm
    intro hpr
    have := (Nat.prime_def_minFac).mp hpr
    omega

/-- The harmonic leaf, from the fold of the rounded reciprocals. -/
public theorem phiEnclosure_of_fold {t S A C : ℕ} (hS : Nat.blt 0 S = true)
    (hA : sumB (recipPlain S) 1 t 1 = A) (hC : Nat.beq t C = true) :
    PhiEnclosure t 1 A (A + C) S := by
  have h := phiB_one_mem_Icc_of_fold hS hA hC
  rw [PhiEnclosure, Set.mem_Icc]
  rw [Set.mem_Icc] at h
  push_cast
  exact h

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
