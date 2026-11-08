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

end PrimeCert
