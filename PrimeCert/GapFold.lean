/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.PrimeHarmonic

import PrimeCert.ForLean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Monotone.Basic

/-!
# A windowed batch summed by walking the gaps between its set bits

`gapFoldK P Q PQ F M G lo S c` walks the `c` gaps packed `F` bits apart in `G`, each read through
the mask `M`, carrying in one natural number the window it rebuilds (below `P`), the position it
has reached (the next `Q` values) and the running total above that. Each step adds the next gap to
the position, sets that bit of the rebuilt window and adds `S / value (lo + position)` to the total.
The position starts at `0`, so with every gap at least one the first bit set is at position `1` or
above, and the rebuilt window is the batch's own window shifted up one place.

`gapFoldK_div` is the bridge: when the rebuilt window is `w <<< 1`, the total is
`sumB (recipAtW w (lo + 1) S) 0 B 1`, the fold the production path computes bit by bit. The
elaborator-side `gapPos`, `gapWin` and `gapTot` describe the three fields, `gapFoldK_eq` shows the
state is their packing, `gapWin_testBit` reads the rebuilt window's bits as the positions reached,
and the strictly increasing positions make the total a sum over the set bits.
-/

namespace PrimeCert

open Finset

/-! ## The kernel-side walk -/

/-- One number holding, from the bottom, the rebuilt window (below `P`), the position reached (in
`Q` values above that), and the total above both; `PQ` is `P * Q`. Gap `i` is the field of `G`
starting at bit `F * i`, read through the mask `M`. -/
@[expose] public noncomputable def gapFoldK (P Q PQ F M G lo S c : ℕ) : ℕ :=
  c.rec (nat_lit 0) fun i st ↦
    Nat.add
      (Nat.lor (Nat.mod st P)
        (Nat.shiftLeft (nat_lit 1)
          (Nat.add (Nat.mod (Nat.div st P) Q) (Nat.land (Nat.shiftRight G (Nat.mul F i)) M))))
      (Nat.mul P
        (Nat.add
          (Nat.add (Nat.mod (Nat.div st P) Q) (Nat.land (Nat.shiftRight G (Nat.mul F i)) M))
          (Nat.mul Q
            (Nat.add (Nat.div st PQ)
              (Nat.div S
                (Sieve.valueK
                  (Nat.add lo
                    (Nat.add (Nat.mod (Nat.div st P) Q)
                      (Nat.land (Nat.shiftRight G (Nat.mul F i)) M)))))))))

/-- The position reached after `c` gaps, in the operations the kernel reads. -/
@[expose] public noncomputable def gapWalkK (F M G c : ℕ) : ℕ :=
  c.rec (nat_lit 0) fun i p ↦ Nat.add p (Nat.land (Nat.shiftRight G (Nat.mul F i)) M)

/-- Whether each of the first `c` gaps is at least one. -/
@[expose] public noncomputable def gapsPosK (F M G c : ℕ) : Bool :=
  c.rec true fun i b ↦
    Bool.and' b (Nat.blt (nat_lit 0) (Nat.land (Nat.shiftRight G (Nat.mul F i)) M))

/-! ## The three fields, elaborator side -/

/-- Gap `i`: the field of `G` starting at bit `F * i`, read through the mask `M`. -/
def gapAt (F M G i : ℕ) : ℕ := (G >>> (F * i)) &&& M

/-- The position reached after `i` gaps, starting from `0`. -/
def gapPos (F M G : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => gapPos F M G i + gapAt F M G i

/-- The window rebuilt after `i` gaps: a bit at each position reached. -/
def gapWin (F M G : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => gapWin F M G i ||| 2 ^ gapPos F M G (i + 1)

/-- The total after `i` gaps: `S / value (lo + position)` summed over the positions reached. -/
def gapTot (F M G lo S : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => gapTot F M G lo S i + S / Sieve.value (lo + gapPos F M G (i + 1))

/-- One step of `gapFoldK` on the packed state `st`, for the proof to unfold. -/
def gapStep (P Q PQ F M G lo S i st : ℕ) : ℕ :=
  Nat.add
    (Nat.lor (Nat.mod st P)
      (Nat.shiftLeft (nat_lit 1)
        (Nat.add (Nat.mod (Nat.div st P) Q) (Nat.land (Nat.shiftRight G (Nat.mul F i)) M))))
    (Nat.mul P
      (Nat.add
        (Nat.add (Nat.mod (Nat.div st P) Q) (Nat.land (Nat.shiftRight G (Nat.mul F i)) M))
        (Nat.mul Q
          (Nat.add (Nat.div st PQ)
            (Nat.div S
              (Sieve.valueK
                (Nat.add lo
                  (Nat.add (Nat.mod (Nat.div st P) Q)
                    (Nat.land (Nat.shiftRight G (Nat.mul F i)) M)))))))))

theorem gapFoldK_succ (P Q PQ F M G lo S c : ℕ) :
    gapFoldK P Q PQ F M G lo S (c + 1)
      = gapStep P Q PQ F M G lo S c (gapFoldK P Q PQ F M G lo S c) :=
  rfl

theorem gapWalkK_succ (F M G c : ℕ) :
    gapWalkK F M G (c + 1)
      = Nat.add (gapWalkK F M G c) (Nat.land (Nat.shiftRight G (Nat.mul F c)) M) :=
  rfl

theorem gapsPosK_succ (F M G c : ℕ) :
    gapsPosK F M G (c + 1)
      = Bool.and' (gapsPosK F M G c)
          (Nat.blt (nat_lit 0) (Nat.land (Nat.shiftRight G (Nat.mul F c)) M)) :=
  rfl

theorem gapWalkK_eq (F M G c : ℕ) : gapWalkK F M G c = gapPos F M G c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [gapWalkK_succ, ih, gapPos, gapAt, Nat.add_eq, Nat.land_eq, Nat.shiftRight_eq', Nat.mul_eq]

theorem gapsPosK_eq (F M G c : ℕ) : gapsPosK F M G c = true ↔ ∀ i < c, 0 < gapAt F M G i := by
  induction c with
  | zero => exact ⟨fun _ i hi ↦ absurd hi (Nat.not_lt_zero i), fun _ ↦ rfl⟩
  | succ c ih =>
    rw [gapsPosK_succ, Bool.and'_eq_and, Bool.and_eq_true, ih, Nat.blt_eq]
    simp only [gapAt, Nat.land_eq, Nat.shiftRight_eq', Nat.mul_eq]
    constructor
    · rintro ⟨h, hc⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
      · exact h i h'
      · exact hc
    · intro h
      exact ⟨fun i hi ↦ h i (Nat.lt_succ_of_lt hi), h c (Nat.lt_succ_self c)⟩

/-! ## Positions increase, the window records them, the state packs all three -/

theorem gapPos_monotone (F M G : ℕ) : Monotone (gapPos F M G) :=
  monotone_nat_of_le_succ fun i ↦ by rw [gapPos]; exact Nat.le_add_right _ _

theorem gapPos_lt {F M G c : ℕ} (hpos : ∀ i < c, 0 < gapAt F M G i) {i j : ℕ} (hij : i < j)
    (hj : j ≤ c) : gapPos F M G i < gapPos F M G j := by
  induction j with
  | zero => omega
  | succ j _ =>
    have h1 := gapPos_monotone F M G (Nat.lt_succ_iff.mp hij)
    have h2 := hpos j (by omega)
    rw [gapPos]
    omega

theorem gapWin_testBit (F M G i k : ℕ) :
    (gapWin F M G i).testBit k = true ↔ ∃ j, 0 < j ∧ j ≤ i ∧ gapPos F M G j = k := by
  induction i with
  | zero =>
    rw [gapWin, Nat.zero_testBit]
    exact ⟨fun h ↦ absurd h Bool.false_ne_true,
      fun ⟨_, h0, hi, _⟩ ↦ absurd (h0.trans_le hi) (lt_irrefl 0)⟩
  | succ i ih =>
    rw [gapWin, Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨j, hj0, hji, rfl⟩ | rfl)
      · exact ⟨j, hj0, hji.trans (Nat.le_succ i), rfl⟩
      · exact ⟨i + 1, Nat.succ_pos i, le_rfl, rfl⟩
    · rintro ⟨j, hj0, hji, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hji) with h | h
      · exact Or.inl ⟨j, hj0, Nat.lt_succ_iff.mp h, rfl⟩
      · exact Or.inr (by rw [h])

theorem gapWin_lt (F M G : ℕ) {i Pb : ℕ} (h : gapPos F M G i < Pb) : gapWin F M G i < 2 ^ Pb := by
  induction i with
  | zero =>
    rw [gapWin]
    exact Nat.two_pow_pos Pb
  | succ i ih =>
    rw [gapWin]
    refine Nat.or_lt_two_pow (ih ((gapPos_monotone F M G (Nat.le_succ i)).trans_lt h)) ?_
    exact Nat.pow_lt_pow_right Nat.one_lt_two h

/-- The state after `c` gaps packs the rebuilt window, the position and the total, as long as the
position stays below `Q` and below the width of the window field. -/
theorem gapFoldK_eq (P Q PQ F M G lo S : ℕ) {Pb c : ℕ} (hP : P = 2 ^ Pb) (hPQ : PQ = P * Q)
    (hQ : gapPos F M G c < Q) (hPb : gapPos F M G c < Pb) :
    gapFoldK P Q PQ F M G lo S c
      = gapWin F M G c + P * (gapPos F M G c + Q * gapTot F M G lo S c) := by
  induction c with
  | zero => simp [gapFoldK, gapWin, gapPos, gapTot]
  | succ c ih =>
    have hmono := gapPos_monotone F M G (Nat.le_succ c)
    have hQ' := hmono.trans_lt hQ
    have hW := gapWin_lt F M G (hmono.trans_lt hPb)
    rw [← hP] at hW
    have hQ0 : 0 < Q := by omega
    have hP0 : 0 < P := by omega
    rw [gapFoldK_succ, ih hQ' (hmono.trans_lt hPb), gapStep]
    simp only [Nat.add_eq, Nat.mul_eq, Nat.mod_eq_mod, Nat.div_eq_div, Nat.lor_eq, Nat.land_eq,
      Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.one_shiftLeft, Sieve.valueK_eq_value]
    rw [hPQ, ← Nat.div_div_eq_div_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hW,
      Nat.add_mul_div_left _ _ hP0, Nat.div_eq_of_lt hW, Nat.zero_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hQ', Nat.add_mul_div_left _ _ hQ0, Nat.div_eq_of_lt hQ', Nat.zero_add]
    simp only [gapWin, gapPos, gapTot, gapAt]

theorem gapTot_eq_sum (F M G lo S c : ℕ) :
    gapTot F M G lo S c = ∑ i ∈ range c, S / Sieve.value (lo + gapPos F M G (i + 1)) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [gapTot, ih, Finset.sum_range_succ]

/-! ## The bridge -/

/-- The gap walk's total is the windowed reciprocal fold. Every hypothesis is a Boolean literal the
emitter discharges by reflection: `hP` and `hPQ` fix the two field boundaries, `hQ` and `hPb` keep
the final position (and so every position) inside the position field and the window field, `hgaps`
says every gap is at least one, `hw` bounds the window by its `B` bits, and `htie` says the rebuilt
window is `w` shifted up one place. -/
public theorem gapFoldK_div (P Q PQ Pb F M G lo S c w B : ℕ)
    (hP : Nat.beq P (Nat.pow (nat_lit 2) Pb) = true) (hPQ : Nat.beq PQ (Nat.mul P Q) = true)
    (hQ : Nat.blt (gapWalkK F M G c) Q = true) (hPb : Nat.blt (gapWalkK F M G c) Pb = true)
    (hgaps : gapsPosK F M G c = true) (hw : Nat.blt w (Nat.pow (nat_lit 2) B) = true)
    (htie : Nat.beq (Nat.mod (gapFoldK P Q PQ F M G lo S c) P)
      (Nat.shiftLeft w (nat_lit 1)) = true) :
    Nat.div (gapFoldK P Q PQ F M G lo S c) PQ = sumB (recipAtW w (lo + 1) S) 0 B 1 := by
  rw [Nat.beq_eq] at hP hPQ htie
  rw [Nat.blt_eq, gapWalkK_eq] at hQ hPb
  rw [Nat.blt_eq, Nat.pow_eq] at hw
  rw [Nat.pow_eq] at hP
  rw [Nat.mul_eq] at hPQ
  rw [gapsPosK_eq] at hgaps
  have hdec := gapFoldK_eq P Q PQ F M G lo S hP hPQ hQ hPb
  have hW := gapWin_lt F M G hPb
  rw [← hP] at hW
  have hQ0 : 0 < Q := by omega
  have hP0 : 0 < P := by omega
  rw [Nat.mod_eq_mod, Nat.shiftLeft_eq', hdec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hW]
    at htie
  rw [Nat.div_eq_div, hdec, hPQ, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hP0,
    Nat.div_eq_of_lt hW, Nat.zero_add, Nat.add_mul_div_left _ _ hQ0, Nat.div_eq_of_lt hQ,
    Nat.zero_add, gapTot_eq_sum, sumB_eq_sum]
  have hR : ∀ n, recipAtW w (lo + 1) S (n * 1 + 0)
      = if w.testBit n = true then S / Sieve.value (lo + (n + 1)) else 0 := by
    intro n
    rw [recipAtW, Bool.rec_eq, Sieve.testBitK_eq_testBit, Sieve.valueK_eq_value, Nat.div_eq_div,
      Nat.add_eq, Nat.mul_one, Nat.add_zero, Nat.add_right_comm, Nat.add_assoc]
  simp only [hR]
  rw [← Finset.sum_filter]
  have hinj : ∀ x ∈ range c, ∀ y ∈ range c,
      gapPos F M G (x + 1) = gapPos F M G (y + 1) → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_range] at hx hy
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd hxy (gapPos_lt hgaps (Nat.succ_lt_succ h) hy).ne
    · exact absurd hxy (gapPos_lt hgaps (Nat.succ_lt_succ h) hx).ne'
  have hinj2 : ∀ x ∈ (range B).filter (fun n ↦ w.testBit n = true),
      ∀ y ∈ (range B).filter (fun n ↦ w.testBit n = true), x + 1 = y + 1 → x = y :=
    fun x _ y _ h ↦ Nat.succ_injective h
  have hset : (range c).image (fun i ↦ gapPos F M G (i + 1))
      = ((range B).filter (fun n ↦ w.testBit n = true)).image (fun n ↦ n + 1) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    have hk : (gapWin F M G c).testBit k = (w <<< 1).testBit k := by rw [htie]
    rw [Nat.testBit_shiftLeft] at hk
    constructor
    · rintro ⟨i, hi, rfl⟩
      have h1 : (gapWin F M G c).testBit (gapPos F M G (i + 1)) = true :=
        (gapWin_testBit F M G c _).mpr ⟨i + 1, Nat.succ_pos i, hi, rfl⟩
      rw [hk, Bool.and_eq_true, decide_eq_true_iff] at h1
      refine ⟨gapPos F M G (i + 1) - 1, ⟨?_, h1.2⟩, by omega⟩
      by_contra hB
      have h2 := h1.2
      rw [Nat.testBit_lt_two_pow
        (hw.trans_le (Nat.pow_le_pow_right Nat.two_pos (not_lt.mp hB)))] at h2
      exact absurd h2 Bool.false_ne_true
    · rintro ⟨n, ⟨_, hbit⟩, rfl⟩
      have h1 : (gapWin F M G c).testBit (n + 1) = true := by
        rw [hk, Bool.and_eq_true, decide_eq_true_iff, Nat.add_sub_cancel]
        exact ⟨by omega, hbit⟩
      obtain ⟨j, hj0, hjc, hjk⟩ := (gapWin_testBit F M G c (n + 1)).mp h1
      refine ⟨j - 1, by omega, ?_⟩
      rw [Nat.sub_add_cancel hj0]
      exact hjk
  have e1 := Finset.sum_image (f := fun k ↦ S / Sieve.value (lo + k)) hinj
  have e2 := Finset.sum_image (f := fun k ↦ S / Sieve.value (lo + k)) hinj2
  rw [← e1, hset, e2]

/-- `gapFoldK_div` with the fold's value `R` as its own literal, so that the kernel check of the
fold and the tie to the window are the declarations `run_gap` emits, and the division is a
literal the emitter computes. -/
public theorem gapFoldK_div_lit (P Q PQ Pb F M G lo lo1 S c w B R A : ℕ)
    (hP : Nat.beq P (Nat.pow (nat_lit 2) Pb) = true) (hPQ : Nat.beq PQ (Nat.mul P Q) = true)
    (hQ : Nat.blt (gapWalkK F M G c) Q = true) (hPb : Nat.blt (gapWalkK F M G c) Pb = true)
    (hgaps : gapsPosK F M G c = true) (hw : Nat.blt w (Nat.pow (nat_lit 2) B) = true)
    (hlo : Nat.beq (Nat.add lo (nat_lit 1)) lo1 = true)
    (hR : Nat.beq (gapFoldK P Q PQ F M G lo S c) R = true)
    (htie : Nat.beq (Nat.mod R P) (Nat.shiftLeft w (nat_lit 1)) = true)
    (hA : Nat.beq (Nat.div R PQ) A = true) :
    sumB (recipAtW w lo1 S) (nat_lit 0) B (nat_lit 1) = A := by
  rw [Nat.beq_eq] at hlo hR hA
  subst hlo hR hA
  rw [Nat.add_eq]
  exact (gapFoldK_div P Q PQ Pb F M G lo S c w B hP hPQ hQ hPb hgaps hw htie).symm

/-- `sumB_windowEqR` taking the batch's total as an equation rather than as a Boolean test, which
is the form `gapFoldK_div_lit` concludes in. -/
public theorem sumB_windowEqG (f g : ℕ → ℕ) (start len t : ℕ)
    (hb : sumB f start len (nat_lit 1) = sumB g (nat_lit 0) len (nat_lit 1))
    (h : sumB g (nat_lit 0) len (nat_lit 1) = t) :
    sumB f start len (nat_lit 1) = t := hb.trans h

end PrimeCert
