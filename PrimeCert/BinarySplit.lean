/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Init
public import Mathlib.Algebra.Order.Field.Rat

import Mathlib.Tactic.FieldSimp

/-!
# A binary split over the naturals

A series whose consecutive terms stand in a rational ratio is summed here by splitting the range
in two, summing each half as a single numerator over a single denominator, and combining the two.
`binarySplit p q m n` returns `(T, Q, P)` with

* `∑_{m ≤ i < n} ∏_{m ≤ j ≤ i} (p j / q j) = T / Q`, and
* `∏_{m ≤ j < n} (p j / q j) = P / Q`,

where `Q` is the product of the `q j`, so no redundant factor is carried.

The three certificate lemmas at the end (`binarySplit_of_le`, `binarySplit_of_base`,
`binarySplit_rec`) are what an emitted proof is built from: each carries its result tuple as
literals, tied to the inputs by `Nat.beq`, so a metaprogram computes the tuple and the kernel only
decides equalities between numerals. The wider bases collapse a whole subtree into one application
of the same shape.
-/

namespace PrimeCert

open Finset

/-- The sum and product of a ratio-driven series over `Ico m n`, as `(T, Q, P)`: the sum is `T/Q`,
the running product is `P/Q`, and `Q` is the product of the `q j`. -/
public def binarySplit (p q : ℕ → ℕ) (m n : ℕ) : ℕ × ℕ × ℕ :=
  if _h : m < n then
    if _h2 : m + 1 = n then (p m, q m, p m)
    else
      let (tl, ql, pl) := binarySplit p q m ((m + n) / 2)
      let (tr, qr, pr) := binarySplit p q ((m + n) / 2) n
      (tl * qr + pl * tr, ql * qr, pl * pr)
  else (0, 1, 1)
termination_by n - m
decreasing_by all_goals omega

/-- The last two components are the two products over the range. -/
public theorem binarySplit_PQ {p q : ℕ → ℕ} {m n : ℕ} :
    (binarySplit p q m n).2.2 = ∏ j ∈ Ico m n, p j ∧
    (binarySplit p q m n).2.1 = ∏ j ∈ Ico m n, q j := by
  fun_induction binarySplit with
  | case1 m hlt => simp [Nat.Ico_succ_singleton]
  | case3 m n => simp_all
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    simp only [hL] at ihL
    simp only [hR] at ihR
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    refine ⟨?_, ?_⟩ <;>
      rw [← prod_Ico_consecutive _ hmk hkn] <;> simp [ihL.1, ihL.2, ihR.1, ihR.2]

/-- The denominator a split returns is never zero. -/
public theorem binarySplit_nonzero {p q : ℕ → ℕ} {m n : ℕ} (hq : ∀ i, q i ≠ 0) :
    (binarySplit p q m n).2.1 ≠ 0 := by
  fun_induction binarySplit <;> simp_all

/-- What the split computes: `T/Q` is the sum of the running products, `P/Q` the whole product. -/
public theorem binarySplit_spec {p q : ℕ → ℕ} {m n T Q P : ℕ} (hq : ∀ i, q i ≠ 0)
    (h : (T, Q, P) = binarySplit p q m n) :
    (∏ j ∈ Ico m n, ((p j : ℚ) / q j) = (P : ℚ) / Q) ∧
    (∑ i ∈ Ico m n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j) = (T : ℚ) / Q) := by
  fun_induction binarySplit generalizing T Q P with
  | case1 m hlt =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hIco : Finset.Ico m (m + 1) = {m} := by
      ext x
      rw [Finset.mem_Ico, Finset.mem_singleton]
      omega
    simp [hIco]
  | case3 m n =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Ico_eq_empty (by omega : ¬ m < n)]
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    specialize ihL hL.symm
    specialize ihR hR.symm
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    obtain ⟨hPl, hSl⟩ := ihL
    obtain ⟨hPr, hSr⟩ := ihR
    have hqtl := binarySplit_nonzero (p := p) (m := m) (n := (m + n) / 2) hq
    simp only [hL] at hqtl
    have hqtr := binarySplit_nonzero (p := p) (m := (m + n) / 2) (n := n) hq
    simp only [hR] at hqtr
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hqlr : (ql : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtl
    have hqrr : (qr : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtr
    constructor
    · rw [← prod_Ico_consecutive _ hmk hkn, hPl, hPr]
      push_cast
      field_simp
    · rw [← sum_Ico_consecutive _ hmk hkn, hSl]
      have hsplit : ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j)
          = ((pl : ℚ) / ql) * ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico ((m + n) / 2) (i + 1),
              ((p j : ℚ) / q j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        simp only [Finset.mem_Ico] at hi
        rw [← prod_Ico_consecutive _ hmk (by omega : (m + n) / 2 ≤ i + 1), hPl]
      rw [hsplit, hSr]
      push_cast
      field_simp

/-! ### The certificate lemmas

Each states the tuple as literals, with the side conditions in the primitive `Nat.beq`,
`Nat.ble`, `Nat.blt` the kernel decides without unfolding notation. -/

/-- `Nat.div` in its primitive form, the companion of `Nat.add_eq` and `Nat.mul_eq`. -/
public theorem Nat.div_eq' {a b : ℕ} : a.div b = a / b := rfl

/-- An empty range. -/
public theorem binarySplit_of_le {p q : ℕ → ℕ} {m n : ℕ} (h : n.ble m) :
    binarySplit p q m n = (0, 1, 1) := by
  rw [binarySplit]
  simp only [Nat.ble_eq] at h
  rw [dif_neg (by omega)]

/-- A single term. -/
public theorem binarySplit_of_base {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.succ).beq n) (hT : T.beq (p m)) (hQ : Q.beq (q m)) (hP : P.beq (p m)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  rw [binarySplit, dif_pos (by omega), dif_pos rfl]

/-- Two halves combined. -/
public theorem binarySplit_rec {p q : ℕ → ℕ}
    {m n k tl ql pl tr qr pr T Q P : ℕ}
    (h1 : (m.succ).blt n) (hk : k.beq ((m.add n).div 2))
    (hT : T.beq ((tl.mul qr).add (pl.mul tr))) (hQ : Q.beq (ql.mul qr))
    (hP : P.beq (pl.mul pr))
    (hl : binarySplit p q m k = (tl, ql, pl))
    (hr : binarySplit p q k n = (tr, qr, pr)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.div_eq'] at h1 hk hT hQ hP
  subst hk hT hQ hP
  rw [binarySplit, dif_pos (by omega), dif_neg (by omega), hl, hr]

/-! The wider bases below collapse a two- to four-term subtree into one application, so an emitted
proof names one node where the leaf/leaf/`binarySplit_rec` shape named three or seven. They are
the same combines over the same midpoints, so the literals match the narrow tree's exactly. -/

/-- Two terms. -/
public theorem binarySplit_of_base2 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 2).beq n)
    (hT : T.beq (((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))))
    (hQ : Q.beq ((q m).mul (q (m.succ))))
    (hP : P.beq ((p m).mul (p (m.succ)))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 2) = (p (m + 1), q (m + 1), p (m + 1)) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

/-- Three terms. -/
public theorem binarySplit_of_base3 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 3).beq n)
    (hT : T.beq (((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add
      ((p m).mul (((p (m.succ)).mul (q (m.add 2))).add
        ((p (m.succ)).mul (p (m.add 2)))))))
    (hQ : Q.beq ((q m).mul ((q (m.succ)).mul (q (m.add 2)))))
    (hP : P.beq ((p m).mul ((p (m.succ)).mul (p (m.add 2))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 3) =
      (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2), q (m + 1) * q (m + 2),
        p (m + 1) * p (m + 2)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

/-- Four terms. -/
public theorem binarySplit_of_base4 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 4).beq n)
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul
        ((q (m.add 2)).mul (q (m.add 3)))).add
      (((p m).mul (p (m.succ))).mul
        (((p (m.add 2)).mul (q (m.add 3))).add ((p (m.add 2)).mul (p (m.add 3)))))))
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))))
    (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 4) =
      (p (m + 2) * q (m + 3) + p (m + 2) * p (m + 3), q (m + 2) * q (m + 3),
        p (m + 2) * p (m + 3)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

end PrimeCert
