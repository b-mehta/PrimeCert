/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.SegmentedSieve

/-! # The batch proofs, generalised over the lane width

Staged here, to move into `PrimeCert/SegmentedSieve.lean` beside the lemmas they mirror. They live
in a file of their own meanwhile because they depend on declarations from the middle of that file
and are easier to check against it from outside: `lake env lean` on this takes seconds where
rebuilding the module takes minutes.

Each mirrors the three-bit lemma of the same name. The lane width appears in those proofs only as
an opaque scrutinee, so the arguments carry over unchanged, which is the whole reason a wider band
does not need a second copy of them.

**What these do not cover.** They are the *record* side: how an entry decodes, which slice it lands
in, and what a finished batch holds. The *mask* side is still three-bit-specific, because
`testBit_segAccLoopSK_band8` rests on a decomposition of the mask into exactly eight strikes
(`buildMaskCK_octave`, `testBit_seedOct`, and one seed lemma per lane). A sixteen-strike band needs
that decomposition again at sixteen, and that is new content rather than a substitution. It is the
remaining cost of the octave below. -/

namespace PrimeCert.Sieve

/-- `entryHits` with the lane width left open. -/
@[expose] public noncomputable def entryHitsL (lw c lo start k len j e : Nat) : Bool :=
  testBitK c (e.shiftRight lw) && Nat.beq ((entrySeedLK lw lo start e).shiftRight 16) k &&
    (Nat.beq j ((entrySeedLK lw lo start e).land 65535) || Nat.beq j (entryTallyLK lw len e))

/-- `outHits` with the lane width left open. -/
@[expose] public noncomputable def outHitsL (lw c lo start Wm1 len j e : Nat) : Bool :=
  testBitK c (e.shiftRight lw) && Nat.blt Wm1 (entrySeedLK lw lo start e) &&
    Nat.beq j (entryTallyLK lw len e)

/-- `stripeStateK` with the lane width left open. -/
@[expose] public noncomputable def stripeStateLK
    (lw c lo start len Wm1 slotW Ls Cs np k : Nat) : Nat :=
  (Nat.beq k np).rec
    (stripeSlotLK lw c lo start k len
      ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
      ((Cs.shiftRight (k.mul 16)).land 65535) 0)
    (stripeOutSlotLK lw c lo start Wm1 len
      ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
      ((Cs.shiftRight (k.mul 16)).land 65535) 0)

public theorem stripeStateLK_three {c lo start len Wm1 slotW Ls Cs np k : Nat} :
    stripeStateLK 3 c lo start len Wm1 slotW Ls Cs np k
      = stripeStateK c lo start len Wm1 slotW Ls Cs np k := rfl

/-- A step of a slice's list, one bit at a time. -/
public theorem testBit_stripeEntryLK {lw st c lo start k len e j : Nat} :
    (stripeEntryLK lw st c lo start k len e).testBit j
      = (st.testBit j || entryHitsL lw c lo start k len j e) := by
  unfold entryHitsL
  unfold stripeEntryLK
  cases hc : testBitK c (e.shiftRight lw) with
  | false => simp
  | true =>
    cases hk : Nat.beq ((entrySeedLK lw lo start e).shiftRight 16) k with
    | false => simp
    | true =>
      have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
      rw [hlor, hlor, Nat.testBit_or, Nat.testBit_or, testBit_oneShift, testBit_oneShift]
      simp

/-- A step of the out-of-window list, one bit at a time. -/
public theorem testBit_stripeOutLK {lw st c lo start Wm1 len e j : Nat} :
    (stripeOutLK lw st c lo start Wm1 len e).testBit j
      = (st.testBit j || outHitsL lw c lo start Wm1 len j e) := by
  unfold outHitsL
  unfold stripeOutLK
  cases hc : testBitK c (e.shiftRight lw) with
  | false => simp
  | true =>
    cases hw : Nat.blt Wm1 (entrySeedLK lw lo start e) with
    | false => simp
    | true =>
      have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
      rw [hlor, Nat.testBit_or, testBit_oneShift]
      simp

/-- Walking one more entry. -/
public theorem stripeSlotLK_succ {lw c lo start k len slot cnt st : Nat} :
    stripeSlotLK lw c lo start k len slot (cnt + 1) st
      = stripeEntryLK lw (stripeSlotLK lw c lo start k len slot cnt st) c lo start k len
          ((slot.shiftRight (cnt.mul 16)).land 65535) := rfl

/-- Walking one more entry of the out-of-window list. -/
public theorem stripeOutSlotLK_succ {lw c lo start Wm1 len slot cnt st : Nat} :
    stripeOutSlotLK lw c lo start Wm1 len slot (cnt + 1) st
      = stripeOutLK lw (stripeOutSlotLK lw c lo start Wm1 len slot cnt st) c lo start Wm1 len
          ((slot.shiftRight (cnt.mul 16)).land 65535) := rfl

/-- A bit of a finished list is a bit of what the walk started from, or one that some entry of the
list set. -/
public theorem testBit_stripeSlotLK {lw c lo start k len slot st j : Nat} (cnt : Nat) :
    (stripeSlotLK lw c lo start k len slot cnt st).testBit j = true ↔
      (st.testBit j = true ∨ ∃ m, m < cnt ∧
        entryHitsL lw c lo start k len j ((slot.shiftRight (m.mul 16)).land 65535) = true) := by
  induction cnt with
  | zero =>
    have h : stripeSlotLK lw c lo start k len slot 0 st = st := rfl
    rw [h]
    constructor
    · exact fun hj => Or.inl hj
    · rintro (hj | ⟨m, hm, _⟩)
      · exact hj
      · exact absurd hm (by lia)
  | succ n ih =>
    rw [stripeSlotLK_succ, testBit_stripeEntryLK, Bool.or_eq_true, ih]
    constructor
    · rintro ((hj | ⟨m, hm, he⟩) | hn)
      · exact Or.inl hj
      · exact Or.inr ⟨m, by lia, he⟩
      · exact Or.inr ⟨n, by lia, hn⟩
    · rintro (hj | ⟨m, hm, he⟩)
      · exact Or.inl (Or.inl hj)
      · rcases Nat.lt_or_ge m n with hmn | hmn
        · exact Or.inl (Or.inr ⟨m, hmn, he⟩)
        · have : m = n := by lia
          rw [this] at he
          exact Or.inr he

/-- The same for the out-of-window list. -/
public theorem testBit_stripeOutSlotLK {lw c lo start Wm1 len slot st j : Nat} (cnt : Nat) :
    (stripeOutSlotLK lw c lo start Wm1 len slot cnt st).testBit j = true ↔
      (st.testBit j = true ∨ ∃ m, m < cnt ∧
        outHitsL lw c lo start Wm1 len j ((slot.shiftRight (m.mul 16)).land 65535) = true) := by
  induction cnt with
  | zero =>
    have h : stripeOutSlotLK lw c lo start Wm1 len slot 0 st = st := rfl
    rw [h]
    constructor
    · exact fun hj => Or.inl hj
    · rintro (hj | ⟨m, hm, _⟩)
      · exact hj
      · exact absurd hm (by lia)
  | succ n ih =>
    rw [stripeOutSlotLK_succ, testBit_stripeOutLK, Bool.or_eq_true, ih]
    constructor
    · rintro ((hj | ⟨m, hm, he⟩) | hn)
      · exact Or.inl hj
      · exact Or.inr ⟨m, by lia, he⟩
      · exact Or.inr ⟨n, by lia, hn⟩
    · rintro (hj | ⟨m, hm, he⟩)
      · exact Or.inl (Or.inl hj)
      · rcases Nat.lt_or_ge m n with hmn | hmn
        · exact Or.inl (Or.inr ⟨m, hmn, he⟩)
        · have : m = n := by lia
          rw [this] at he
          exact Or.inr he

/-- The list of seeds past the end of the window sets only tally bits, so it contributes nothing to
the window itself. -/
public theorem stripeOutSlotLK_low {lw c lo start Wm1 len slot cnt b : Nat} (hb : b < 65536) :
    (stripeOutSlotLK lw c lo start Wm1 len slot cnt 0).testBit b = false := by
  rcases Bool.eq_false_or_eq_true
    ((stripeOutSlotLK lw c lo start Wm1 len slot cnt 0).testBit b) with h | h
  · rcases (testBit_stripeOutSlotLK cnt).mp h with hz | ⟨m, _, he⟩
    · simp at hz
    · unfold outHitsL at he
      have hj := (Bool.and_eq_true ..).mp he
      have hbeq : b = entryTallyLK lw len ((slot.shiftRight (m.mul 16)).land 65535) :=
        Nat.eq_of_beq_eq_true hj.2
      have hge : 65536 ≤ entryTallyLK lw len ((slot.shiftRight (m.mul 16)).land 65535) := by
        unfold entryTallyLK
        lia
      exact absurd hbeq (by lia)
  · exact h

/-- One more slice. -/
public theorem stripeUpToLK_succ {lw c lo start len W Wm1 slotW Ls Cs np n : Nat} :
    stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np (n + 1)
      = ((stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np n).lor
          (((stripeStateLK lw c lo start len Wm1 slotW Ls Cs np n).land
            (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (n.mul 65536))).lor
        (((stripeStateLK lw c lo start len Wm1 slotW Ls Cs np n).shiftRight 65536).shiftLeft W) :=
  rfl

/-- Below the window's width, a bit of the assembled number comes from exactly one slice. -/
public theorem testBit_stripeUpToLK_low {lw c lo start len W Wm1 slotW Ls Cs np j : Nat}
    (hj : j < W) (n : Nat) :
    (stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np n).testBit j = true ↔
      ∃ k, k < n ∧ k * 65536 ≤ j ∧ j - k * 65536 < 65536 ∧
        (stripeStateLK lw c lo start len Wm1 slotW Ls Cs np k).testBit (j - k * 65536) = true := by
  induction n with
  | zero =>
    have h : stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np 0 = 0 := rfl
    rw [h]
    constructor
    · intro hb
      simp at hb
    · rintro ⟨k, hk, _⟩
      exact absurd hk (by lia)
  | succ m ih =>
    have hlor : ∀ u v : Nat, u.lor v = u ||| v := fun _ _ => rfl
    rw [stripeUpToLK_succ, hlor, hlor, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true,
      Bool.or_eq_true, ih]
    have hhigh : (((stripeStateLK lw c lo start len Wm1 slotW Ls Cs np m).shiftRight
        65536).shiftLeft W).testBit j = false := by
      rw [testBit_shiftUp]
      have : ¬ W ≤ j := by lia
      simp [this]
    have hmid : (((stripeStateLK lw c lo start len Wm1 slotW Ls Cs np m).land
        (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (m.mul 65536)).testBit j
        = (decide (m * 65536 ≤ j) &&
            ((stripeStateLK lw c lo start len Wm1 slotW Ls Cs np m).testBit (j - m * 65536) &&
              decide (j - m * 65536 < 65536))) := by
      have hm : m.mul 65536 = m * 65536 := rfl
      rw [testBit_shiftUp, hm, testBit_maskLow]
    rw [hhigh, hmid]
    constructor
    · rintro ((⟨k, hk, h1, h2, h3⟩ | hmid') | hfalse)
      · exact ⟨k, by lia, h1, h2, h3⟩
      · have h := Bool.and_eq_true .. |>.mp hmid'
        have h' := Bool.and_eq_true .. |>.mp h.2
        exact ⟨m, by lia, by simpa using h.1, by simpa using h'.2, h'.1⟩
      · simp at hfalse
    · rintro ⟨k, hk, h1, h2, h3⟩
      rcases Nat.lt_or_ge k m with hkm | hkm
      · exact Or.inl (Or.inl ⟨k, hkm, h1, h2, h3⟩)
      · have hkeq : k = m := by lia
        rw [hkeq] at h1 h2 h3
        refine Or.inl (Or.inr ?_)
        simp [h1, h2, h3]

/-- At or above the window's width, a bit of the assembled number is one of the tally bits. -/
public theorem testBit_stripeUpToLK_high {lw c lo start len W Wm1 slotW Ls Cs np j : Nat}
    (hj : W ≤ j) (hW : np * 65536 ≤ W) (n : Nat) (hn : n ≤ np + 1) :
    (stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np n).testBit j = true ↔
      ∃ k, k < n ∧
        (stripeStateLK lw c lo start len Wm1 slotW Ls Cs np k).testBit (65536 + (j - W))
          = true := by
  induction n with
  | zero =>
    have h : stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np 0 = 0 := rfl
    rw [h]
    constructor
    · intro hb
      simp at hb
    · rintro ⟨k, hk, _⟩
      exact absurd hk (by lia)
  | succ m ih =>
    have hlor : ∀ u v : Nat, u.lor v = u ||| v := fun _ _ => rfl
    rw [stripeUpToLK_succ, hlor, hlor, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true,
      Bool.or_eq_true, ih (by lia)]
    have hmid : (((stripeStateLK lw c lo start len Wm1 slotW Ls Cs np m).land
        (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (m.mul 65536)).testBit j = false := by
      have hm : m.mul 65536 = m * 65536 := rfl
      rw [testBit_shiftUp, hm, testBit_maskLow]
      rcases Nat.lt_or_ge m np with hlt | hge
      · have : ¬ (j - m * 65536 < 65536) := by
          have h1 : (m + 1) * 65536 ≤ np * 65536 := Nat.mul_le_mul_right 65536 (by lia)
          lia
        simp [this]
      · have hm64 : m = np := by lia
        rw [hm64]
        rcases Nat.lt_or_ge (j - np * 65536) 65536 with hb | hb
        · have hst : (stripeStateLK lw c lo start len Wm1 slotW Ls Cs np np).testBit
              (j - np * 65536) = false := by
            have hdef : stripeStateLK lw c lo start len Wm1 slotW Ls Cs np np
                = stripeOutSlotLK lw c lo start Wm1 len
                  ((Ls.shiftRight (slotW.mul np)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
                  ((Cs.shiftRight (np.mul 16)).land 65535) 0 := by
              have hbeq : Nat.beq np np = true := Nat.beq_eq.mpr rfl
              unfold stripeStateLK
              rw [hbeq]
            rw [hdef]
            exact stripeOutSlotLK_low hb
          simp [hst]
        · simp [Nat.not_lt_of_ge hb]
    have hhigh : (((stripeStateLK lw c lo start len Wm1 slotW Ls Cs np m).shiftRight
        65536).shiftLeft W).testBit j
        = (stripeStateLK lw c lo start len Wm1 slotW Ls Cs np m).testBit (65536 + (j - W)) := by
      have hsr : ∀ u v b : Nat, (u.shiftRight v).testBit b = u.testBit (v + b) := by
        intro u v b
        have h : u.shiftRight v = u >>> v := rfl
        rw [h, Nat.testBit_shiftRight]
      rw [testBit_shiftUp, hsr]
      simp [hj]
    rw [hmid, hhigh]
    constructor
    · rintro ((⟨k, hk, h3⟩ | hf) | hlast)
      · exact ⟨k, by lia, h3⟩
      · simp at hf
      · exact ⟨m, by lia, hlast⟩
    · rintro ⟨k, hk, h3⟩
      rcases Nat.lt_or_ge k m with hkm | hkm
      · exact Or.inl (Or.inl ⟨k, hkm, h3⟩)
      · have hkeq : k = m := by lia
        rw [hkeq] at h3
        exact Or.inr h3

/-- A tally bit of a batch is set once the entry naming it is in its slice's list. -/
public theorem testBit_stripeBatchLK_tally {lw c lo start len W Wm1 slotW Ls Cs np k m : Nat}
    (hW : np * 65536 ≤ W) (hk : k < np) (hm : m < cntOf Cs k)
    (hc : testBitK c ((entryOf Ls slotW k m).shiftRight lw) = true)
    (hk16 : (entrySeedLK lw lo start (entryOf Ls slotW k m)).shiftRight 16 = k) :
    (stripeBatchLK lw c lo start len W Wm1 slotW Ls Cs np).testBit
      (W + ((entryOf Ls slotW k m).shiftRight lw
        + (entryOf Ls slotW k m).land (laneMaskK lw) * len)) = true := by
  have hbatch : stripeBatchLK lw c lo start len W Wm1 slotW Ls Cs np
      = stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np (np + 1) := rfl
  rw [hbatch]
  refine (testBit_stripeUpToLK_high (by lia :
    W ≤ W + ((entryOf Ls slotW k m).shiftRight lw
      + (entryOf Ls slotW k m).land (laneMaskK lw) * len)) hW (np + 1) (by lia)).mpr
    ⟨k, by lia, ?_⟩
  have hJ : 65536 + (W + ((entryOf Ls slotW k m).shiftRight lw
      + (entryOf Ls slotW k m).land (laneMaskK lw) * len) - W)
      = 65536 + ((entryOf Ls slotW k m).shiftRight lw
        + (entryOf Ls slotW k m).land (laneMaskK lw) * len) := by lia
  rw [hJ]
  have hstate : stripeStateLK lw c lo start len Wm1 slotW Ls Cs np k
      = stripeSlotLK lw c lo start k len
        ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
        (cntOf Cs k) 0 := by
    unfold stripeStateLK cntOf
    rw [beq_of_ne (by lia : k ≠ np)]
  rw [hstate]
  refine (testBit_stripeSlotLK (cntOf Cs k)).mpr (Or.inr ⟨m, hm, ?_⟩)
  unfold entryHitsL
  exact (Bool.and_eq_true ..).mpr ⟨(Bool.and_eq_true ..).mpr ⟨hc, Nat.beq_eq.mpr hk16⟩,
    (Bool.or_eq_true ..).mpr (Or.inr beq_self)⟩

/-- A position of the window is set in the assembled number exactly when some entry, recorded in
the slice that position falls in, names a divisor of the batch whose seed is that position. -/
public theorem testBit_stripeBatchLK_eq {lw c lo start len W Wm1 slotW Ls Cs np j : Nat}
    (hj : j < W) :
    (stripeBatchLK lw c lo start len W Wm1 slotW Ls Cs np).testBit j = true ↔
      ∃ k m, k < np ∧ m < cntOf Cs k ∧
        testBitK c ((entryOf Ls slotW k m).shiftRight lw) = true ∧
        (entrySeedLK lw lo start (entryOf Ls slotW k m)).shiftRight 16 = k ∧
        entrySeedLK lw lo start (entryOf Ls slotW k m) = j := by
  have hbatch : stripeBatchLK lw c lo start len W Wm1 slotW Ls Cs np
      = stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np (np + 1) := rfl
  rw [hbatch, testBit_stripeUpToLK_low hj (np + 1)]
  constructor
  · rintro ⟨k, hk65, hkle, hklt, hst⟩
    rcases Nat.lt_or_ge k np with hk | hk
    · have hstate : stripeStateLK lw c lo start len Wm1 slotW Ls Cs np k
          = stripeSlotLK lw c lo start k len
            ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
            (cntOf Cs k) 0 := by
        unfold stripeStateLK cntOf
        rw [beq_of_ne (by lia : k ≠ np)]
      rw [hstate] at hst
      rcases (testBit_stripeSlotLK (cntOf Cs k)).mp hst with hz | ⟨m, hm, he⟩
      · simp at hz
      · unfold entryHitsL at he
        have h1 := (Bool.and_eq_true ..).mp he
        have h2 := (Bool.and_eq_true ..).mp h1.1
        have hk16 : (entrySeedLK lw lo start (entryOf Ls slotW k m)).shiftRight 16 = k :=
          Nat.eq_of_beq_eq_true h2.2
        refine ⟨k, m, hk, hm, h2.1, hk16, ?_⟩
        rcases (Bool.or_eq_true ..).mp h1.2 with hseed | htally
        · have hlow : j - k * 65536
              = (entrySeedLK lw lo start (entryOf Ls slotW k m)).land 65535 :=
            Nat.eq_of_beq_eq_true hseed
          rw [shiftRight16_eq] at hk16
          rw [land65535_eq] at hlow
          have := Nat.div_add_mod (entrySeedLK lw lo start (entryOf Ls slotW k m)) 65536
          lia
        · have hte : j - k * 65536 = entryTallyLK lw len (entryOf Ls slotW k m) :=
            Nat.eq_of_beq_eq_true htally
          have hge : 65536 ≤ entryTallyLK lw len (entryOf Ls slotW k m) := by
            unfold entryTallyLK
            lia
          exact absurd hte (by lia)
    · have hk64 : k = np := by lia
      rw [hk64] at hst
      have hstate : stripeStateLK lw c lo start len Wm1 slotW Ls Cs np np
          = stripeOutSlotLK lw c lo start Wm1 len
            ((Ls.shiftRight (slotW.mul np)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
            (cntOf Cs np) 0 := by
        have hbeq : Nat.beq np np = true := Nat.beq_eq.mpr rfl
        unfold stripeStateLK cntOf
        rw [hbeq]
      rw [hstate] at hst
      rw [stripeOutSlotLK_low (by lia)] at hst
      simp at hst
  · rintro ⟨k, m, hk, hm, hc, hk16, hseed⟩
    rw [shiftRight16_eq] at hk16
    have hdm := Nat.div_add_mod (entrySeedLK lw lo start (entryOf Ls slotW k m)) 65536
    have hmod : entrySeedLK lw lo start (entryOf Ls slotW k m) % 65536 < 65536 :=
      Nat.mod_lt _ (by lia)
    refine ⟨k, by lia, by lia, by lia, ?_⟩
    have hstate : stripeStateLK lw c lo start len Wm1 slotW Ls Cs np k
        = stripeSlotLK lw c lo start k len
          ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
          (cntOf Cs k) 0 := by
      unfold stripeStateLK cntOf
      rw [beq_of_ne (by lia : k ≠ np)]
    rw [hstate]
    refine (testBit_stripeSlotLK (cntOf Cs k)).mpr (Or.inr ⟨m, hm, ?_⟩)
    unfold entryHitsL
    have hlow : j - k * 65536 = (entrySeedLK lw lo start (entryOf Ls slotW k m)).land 65535 := by
      rw [land65535_eq]
      lia
    have hbeq : Nat.beq (j - k * 65536)
        ((entrySeedLK lw lo start (entryOf Ls slotW k m)).land 65535) = true := by
      rw [hlow]
      exact beq_self
    have hk16' : Nat.beq ((entrySeedLK lw lo start (entryOf Ls slotW k m)).shiftRight 16) k
        = true := by
      rw [shiftRight16_eq, hk16]
      exact beq_self
    rw [← entryOf_eq, hc, hk16', hbeq]
    simp

/-- A tally bit names one position of the batch and one of a divisor's strikes. -/
public theorem entryTallyLK_inj {lw len e i w : Nat} (hi : (e.shiftRight lw) < len) (hi' : i < len)
    (h : entryTallyLK lw len e = Nat.add 65536 (Nat.add i (Nat.mul w len))) :
    e.shiftRight lw = i ∧ e.land (laneMaskK lw) = w := by
  unfold entryTallyLK at h
  have hlen : 0 < len := by lia
  have hadd : e.shiftRight lw + (e.land (laneMaskK lw)) * len = i + w * len := by lia
  have hmod : (e.shiftRight lw + (e.land (laneMaskK lw)) * len) % len = (i + w * len) % len := by
    rw [hadd]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hi'] at hmod
  refine ⟨hmod, ?_⟩
  have hmul : (e.land (laneMaskK lw)) * len = w * len := by lia
  exact Nat.eq_of_mul_eq_mul_right hlen hmul

/-- Every seed of every divisor the batch holds lands in the assembled number, given that the tally
accounts for it. -/
public theorem stripeBatchLK_complete {lw c lo start len W Wm1 slotW Ls Cs np i w : Nat}
    (hc2 : c < 2 ^ len) (hi : i < len) (hW : np * 65536 ≤ W) (hWm1 : Wm1 < W)
    (htally : (stripeBatchLK lw c lo start len W Wm1 slotW Ls Cs np).testBit
      (W + (i + w * len)) = true)
    (hX : entrySeedLK lw lo start (2 ^ lw * i + w) ≤ Wm1) :
    (stripeBatchLK lw c lo start len W Wm1 slotW Ls Cs np).testBit
      (entrySeedLK lw lo start (2 ^ lw * i + w)) = true := by
  have hbatch : stripeBatchLK lw c lo start len W Wm1 slotW Ls Cs np
      = stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np (np + 1) := rfl
  rw [hbatch] at htally
  obtain ⟨k, hk65, hst⟩ :=
    (testBit_stripeUpToLK_high (by lia : W ≤ W + (i + w * len)) hW (np + 1) (by lia)).mp htally
  have hJ : 65536 + (W + (i + w * len) - W) = 65536 + (i + w * len) := by lia
  rw [hJ] at hst
  -- an entry whose tally bit this is names position `i` and lane `w`
  have hentry : ∀ e : Nat, testBitK c (e.shiftRight lw) = true →
      entryTallyLK lw len e = Nat.add 65536 (Nat.add i (Nat.mul w len)) →
      e = 2 ^ lw * i + w := by
    intro e hce hte
    have hlt : e.shiftRight lw < len := by
      by_contra hge
      rw [testBitK_of_lt hc2 (by lia)] at hce
      simp at hce
    obtain ⟨h1, h2⟩ := entryTallyLK_inj hlt hi hte
    rw [laneMaskK_eq] at h2
    have hsp := entry_splitLw (e := e) (lw := lw)
    lia
  rcases Nat.lt_or_ge k np with hk | hk64
  · have hstate : stripeStateLK lw c lo start len Wm1 slotW Ls Cs np k
        = stripeSlotLK lw c lo start k len
          ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
          (cntOf Cs k) 0 := by
      unfold stripeStateLK cntOf
      rw [beq_of_ne (by lia : k ≠ np)]
    rw [hstate] at hst
    rcases (testBit_stripeSlotLK (cntOf Cs k)).mp hst with hz | ⟨m, hm, he⟩
    · simp at hz
    · unfold entryHitsL at he
      have h1 := (Bool.and_eq_true ..).mp he
      have h2 := (Bool.and_eq_true ..).mp h1.1
      have hbit : testBitK c ((entryOf Ls slotW k m).shiftRight lw) = true := h2.1
      have hk16 : (entrySeedLK lw lo start (entryOf Ls slotW k m)).shiftRight 16 = k :=
        Nat.eq_of_beq_eq_true h2.2
      rcases (Bool.or_eq_true ..).mp h1.2 with hseed | htal
      · have hlow : 65536 + (i + w * len)
            = (entrySeedLK lw lo start (entryOf Ls slotW k m)).land 65535 :=
          Nat.eq_of_beq_eq_true hseed
        rw [land65535_eq] at hlow
        have := Nat.mod_lt (entrySeedLK lw lo start (entryOf Ls slotW k m)) (by lia : 0 < 65536)
        lia
      · have hte : entryTallyLK lw len (entryOf Ls slotW k m)
            = Nat.add 65536 (Nat.add i (Nat.mul w len)) :=
          (Nat.eq_of_beq_eq_true htal).symm
        have heq : entryOf Ls slotW k m = 2 ^ lw * i + w := hentry _ hbit hte
        exact (testBit_stripeBatchLK_eq
          (by lia : entrySeedLK lw lo start (2 ^ lw * i + w) < W)).mpr
          ⟨k, m, hk, hm, hbit, hk16, by rw [heq]⟩
  · have hk64' : k = np := by lia
    rw [hk64'] at hst
    have hstate : stripeStateLK lw c lo start len Wm1 slotW Ls Cs np np
        = stripeOutSlotLK lw c lo start Wm1 len
          ((Ls.shiftRight (slotW.mul np)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
          (cntOf Cs np) 0 := by
      have hbeq : Nat.beq np np = true := Nat.beq_eq.mpr rfl
      unfold stripeStateLK cntOf
      rw [hbeq]
    rw [hstate] at hst
    rcases (testBit_stripeOutSlotLK (cntOf Cs np)).mp hst with hz | ⟨m, hm, he⟩
    · simp at hz
    · unfold outHitsL at he
      have h1 := (Bool.and_eq_true ..).mp he
      have h2 := (Bool.and_eq_true ..).mp h1.1
      have hte : entryTallyLK lw len (entryOf Ls slotW np m)
          = Nat.add 65536 (Nat.add i (Nat.mul w len)) := (Nat.eq_of_beq_eq_true h1.2).symm
      have hbit : testBitK c ((entryOf Ls slotW np m).shiftRight lw) = true := h2.1
      have heq : entryOf Ls slotW np m = 2 ^ lw * i + w := hentry _ hbit hte
      have hblt : Nat.blt Wm1 (entrySeedLK lw lo start (entryOf Ls slotW np m)) = true := h2.2
      rw [heq] at hblt
      have hble : Nat.ble (Wm1 + 1) (entrySeedLK lw lo start (2 ^ lw * i + w)) = true := hblt
      have := Nat.le_of_ble_eq_true hble
      lia

/-! ## The sixteen-strike band

`segLoopSCK_eq_stripe_band8` with the four-bit lane throughout. The three wrappers below exist
only because `2 ^ 4` and `16` are the same term written two ways, which `rw` does not see through.
-/

/-- An entry is its position and its lane, at a four-bit lane. -/
public theorem entry_splitLw4 {e : Nat} : 16 * (e.shiftRight 4) + e.land (laneMaskK 4) = e := by
  rw [laneMaskK_eq]
  exact entry_splitLw (lw := 4)

/-- A four-bit lane is one of sixteen. -/
public theorem landLw_lt4 {e : Nat} : e.land (laneMaskK 4) < 16 := by
  rw [laneMaskK_eq]
  exact landLw_lt (lw := 4)

/-- `stripeBatchLK_complete` with `2 ^ 4` written as the literal it is. -/
public theorem stripeBatchLK_complete4 {c lo start len W Wm1 slotW Ls Cs np i w : Nat}
    (hc2 : c < 2 ^ len) (hi : i < len) (hW : np * 65536 ≤ W) (hWm1 : Wm1 < W)
    (htally : (stripeBatchLK 4 c lo start len W Wm1 slotW Ls Cs np).testBit
      (W + (i + w * len)) = true)
    (hX : entrySeedLK 4 lo start (16 * i + w) ≤ Wm1) :
    (stripeBatchLK 4 c lo start len W Wm1 slotW Ls Cs np).testBit
      (entrySeedLK 4 lo start (16 * i + w)) = true :=
  stripeBatchLK_complete (lw := 4) hc2 hi hW hWm1 htally hX

/-- One batch of the octave below the eight-strike band, settled by sorting its strikes into
slices. -/
public theorem segLoopSCK_eq_stripe_band16 {c lo start len n W Wm1 slotW Ls Cs np seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hc2 : c < 2 ^ len) (hW : np * 65536 ≤ W) (hWm1 : Wm1 < W)
    (hn : 3 ≤ n)
    (hband : ∀ i, i < len → valueK (start + i) * 8 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 16)
    (htal : ∀ i, i < len → ∀ w, w < 16 → testBitK c i = true →
      (stripeBatchLK 4 c lo start len W Wm1 slotW Ls Cs np).testBit
        (W + (i + w * len)) = true) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (stripeBatchLK 4 c lo start len W Wm1 slotW Ls Cs np) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (stripeBatchLK 4 c lo start len W Wm1 slotW Ls Cs np).testBit j = true := by
      constructor
      · intro h
        obtain ⟨i, hi, w, hw, hc, hsd⟩ := (testBit_segAccLoopSK_band16 hj hn hband).mp h
        have hX : entrySeedLK 4 lo start (16 * i + w) ≤ Wm1 := by rw [hsd]; exact hj
        have := stripeBatchLK_complete4 (c := c) (lo := lo) (start := start) (len := len) (W := W)
          (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hc2 hi hW hWm1
          (htal i hi w hw hc) hX
        rwa [hsd] at this
      · intro h
        obtain ⟨k, m, hk, hm, hcbit, hk16, hsd⟩ :=
          (testBit_stripeBatchLK_eq (by lia : j < W)).mp h
        refine (testBit_segAccLoopSK_band16 hj hn hband).mpr
          ⟨(entryOf Ls slotW k m).shiftRight 4, ?_, (entryOf Ls slotW k m).land (laneMaskK 4),
            landLw_lt4, hcbit, ?_⟩
        · by_contra hge
          rw [testBitK_of_lt hc2 (by lia)] at hcbit
          simp at hcbit
        · rw [entry_splitLw4]
          exact hsd
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (stripeBatchLK 4 c lo start len W Wm1 slotW Ls Cs np).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

end PrimeCert.Sieve
