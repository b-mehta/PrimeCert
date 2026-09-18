/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public import PrimeCert.Sieve
public import PrimeCert.SieveCorrect
public import PrimeCert.SieveBase
public import PrimeCert.ForMathlibBitwise
public import Mathlib.Data.Nat.Bitwise

/-!
# A segmented sieve prototype

A window of `W` consecutive mod-6 wheel positions, starting at the wheel index `lo = index a`, is
held in one natural number `seg` used as a `W`-bit bitset: bit `j` of `seg` stands for the number
`value (lo + j)`. `segLoopK` walks the base sieve `s` and, at each index whose bit is set, clears
that prime's multiples from the window.

The translation from the global index space to the window is entirely in the *seeds* of the mask:
the multiples of `p` sit at the global indices `index (5*p) + 2*p*j` and `index (7*p) + 2*p*j`, so
in the window they sit at the local offsets congruent to those seeds modulo `2*p`, and
`firstLocK` computes the smallest such offset. `buildMaskK` from `PrimeCert.Sieve` is then reused
verbatim to grow each seed into a stride-`2*p` mask across the window.

This is a prototype. The kernel-checked statement is the fold equation
`segLoopK s lo Wm1 (initSegK W) 1 fuel = <literal>`; `segmentSound_of` bridges from that to the
absence of small prime factors. See the module note at `SegmentSound`.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Kernel-side definitions -/

/-- A window of `W` live candidates: the low `W` bits set, i.e. `2^W - 1`. -/
@[expose] public def initSegK (W : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 W) 1

/-- The least offset `j` with `lo + j` in the residue class of `A` modulo `m`. -/
@[expose] public def firstLocK (A lo m : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add A (Nat.mul m (Nat.succ (Nat.div lo m)))) lo) m

/-- Clear from the window `seg` every local offset holding a coprime-to-6 multiple of `p`. -/
@[expose] public noncomputable def segMarkK (seg p lo Wm1 : Nat) : Nat :=
  seg.sub (seg.land
    (buildMaskK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
      (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 32))

/-- Sieve the window `seg` by the base primes recorded in the bitset `s`, scanning the base
indices `start, start+1, …` for `fuel` steps. -/
@[expose] public noncomputable def segLoopK (s lo Wm1 seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK s (start.add i)).rec b (segMarkK b (valueK (start.add i)) lo Wm1)

/-! ## The fuel chain -/

/-- Loop recurrence: peel the top index `start+fuel`, in the exact `Bool.rec` form the def uses. -/
public theorem segLoopK_succ {s lo Wm1 seg start fuel : Nat} :
    segLoopK s lo Wm1 seg start (fuel + 1)
      = Bool.rec (segLoopK s lo Wm1 seg start fuel)
          (segMarkK (segLoopK s lo Wm1 seg start fuel) (valueK (start + fuel)) lo Wm1)
          (testBitK s (start + fuel)) := rfl

/-- Fuel additivity: running `a + b` steps is running `a` steps, then `b` more. -/
public theorem segLoopK_add {s lo Wm1 seg start a b : Nat} :
    segLoopK s lo Wm1 seg start (a + b)
      = segLoopK s lo Wm1 (segLoopK s lo Wm1 seg start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [segLoopK_succ]

/-- One chain step: a kernel-checked batch equation moves the run forward by `len` steps. -/
public theorem segLoopK_chain {L s lo Wm1 b b' start len rest : Nat}
    (hP : L = segLoopK s lo Wm1 b start (len.add rest))
    (h : (segLoopK s lo Wm1 b start len).beq b') :
    L = segLoopK s lo Wm1 b' (start.add len) rest := by
  grind [segLoopK_add, Nat.beq_eq]

/-- Last chain step: with no steps left, the batch equation gives the value of the whole run. -/
public theorem segLoopK_last {L s lo Wm1 b b' start len : Nat}
    (hP : L = segLoopK s lo Wm1 b start len)
    (h : (segLoopK s lo Wm1 b start len).beq b') :
    L = b' := by
  grind [Nat.beq_eq]

/-! ## Draft variants, for timing

Two changes to the loop above, kept beside it so that `run_segment_variant` can time them against
it. Each computes the same window as `segLoopK` on every window `seg < 2 ^ (Wm1 + 1)`; that
agreement is checked per batch against the same compiled twin, and is not proved here. -/

/-- `2 ^ A` when `A ≤ M`, and `0` otherwise: a seed bit, dropped when it lies above the window. -/
@[expose] public noncomputable def seedK (A M : Nat) : Nat :=
  (Nat.ble A M).rec 0 (Nat.shiftLeft 1 A)

/-- `seg` with the bits of `hit` cleared, where `hit` is a subset of `seg`; `seg` itself when
`hit = 0`. -/
@[expose] public noncomputable def clearHitK (seg hit : Nat) : Nat :=
  (Nat.ble 1 hit).rec seg (seg.sub hit)

/-- `buildMaskK` with both seeds passed through `seedK`. -/
@[expose] public noncomputable def buildMaskCK (p M A B n : Nat) : Nat :=
  Nat.rec
    ((seedK A M).lor (seedK B M))
    (fun i Mk =>
      ((p.shiftLeft i.succ).ble M).rec Mk
        (Mk.lor (Mk.shiftLeft (p.shiftLeft i.succ))))
    n

/-- `segMarkK` with seeds dropped outside the window, `n` doubling rounds, no rounds at all when
`2 * p > Wm1` (only the seeds can then land in the window), and no subtraction when nothing hits. -/
@[expose] public noncomputable def segMarkCK (seg p lo Wm1 n : Nat) : Nat :=
  ((p.mul 2).ble Wm1).rec
    (clearHitK seg
      (((seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
        (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1)).land seg))
    (clearHitK seg
      ((buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
        (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n).land seg))

/-- `segLoopK` marking with `segMarkCK`. -/
@[expose] public noncomputable def segLoopCK (s lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK s (start.add i)).rec b (segMarkCK b (valueK (start.add i)) lo Wm1 n)

/-- `segLoopK` reading the base primes from a slice `c` of the base sieve: bit `i` of `c` stands for
base index `start + i`. -/
@[expose] public noncomputable def segLoopSK (c lo Wm1 seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkK b (valueK (start.add i)) lo Wm1)

/-- `segLoopSK` marking with `segMarkCK`. -/
@[expose] public noncomputable def segLoopSCK (c lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkCK b (valueK (start.add i)) lo Wm1 n)

/-- The number of terms of `A, A + 2p, A + 4p, …` that can land at or below `M`. -/
@[expose] public noncomputable def termsK (p M : Nat) : Nat :=
  (M.div (p.mul 2)).succ

/-- `buildMaskCK`'s progression built to exactly `termsK p M` terms, by reading the binary digits
of that count from the top down: each round doubles the terms so far, and a set digit adds one more
copy of the seeds. The mask's top bit is then within `2*p` of `M`, where the doubling rounds of
`buildMaskCK` can carry it to nearly `2*M`. `n` counts digits, so `n` must reach the width of
`termsK p M`. -/
@[expose] public noncomputable def buildMaskNK (p M A B n : Nat) : Nat :=
  Nat.rec
    0
    (fun i Mk =>
      let c := (termsK p M).shiftRight (n.sub i)
      let doubled := Mk.lor (Mk.shiftLeft ((p.mul 2).mul c))
      (Nat.beq (((termsK p M).shiftRight (n.sub i.succ)).land 1) 1).rec
        doubled
        (doubled.lor
          (((Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B)).shiftLeft ((p.mul 2).mul (c.mul 2)))))
    n

/-- The same set of positions as `buildMaskCK`, in closed form: the number whose binary digits are
`1` at every multiple of `2*p` below `2*p*k` is `(2 ^ (2*p*k) - 1) / (2 ^ (2*p) - 1)`, and
multiplying it by the two seed bits places the two progressions. No doubling history, and the top
bit lands within `2*p` of `M`. -/
@[expose] public noncomputable def buildMaskRK (p M A B : Nat) : Nat :=
  ((Nat.sub (Nat.pow 2 ((p.mul 2).mul (termsK p M))) 1).div
      (Nat.sub (Nat.pow 2 (p.mul 2)) 1)).mul
    ((Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B))

/-- A seed bit written relative to a 65536-bit slice of the window starting at `base`, and `0` when
the seed lies outside that slice. -/
@[expose] public noncomputable def seedStripeK (A base : Nat) : Nat :=
  (base.ble A).rec 0 (((A.sub base).ble 65535).rec 0 (Nat.shiftLeft 1 (A.sub base)))

/-- One prime's two seeds joined into a 65536-bit slice of the window rather than a number as wide
as the window. For a prime past half the window's width these two bits are all it can hit. -/
@[expose] public noncomputable def stripeMarkK (acc p lo _Wm1 base : Nat) : Nat :=
  acc.lor ((seedStripeK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) base).lor
    (seedStripeK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) base))

/-- `segLoopSCK` writing into a 65536-bit slice through `stripeMarkK`. -/
@[expose] public noncomputable def segLoopStripeK (c lo Wm1 base acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    (testBitK c i).rec a (stripeMarkK a (valueK (start.add i)) lo Wm1 base)

/-- `segMarkCK` with the mask in the closed form of `buildMaskRK`. -/
@[expose] public noncomputable def segMarkRK (seg p lo Wm1 : Nat) : Nat :=
  clearHitK seg
    ((buildMaskRK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
      (firstLocK (indexK (p.mul 7)) lo (p.mul 2))).land seg)

/-- `segLoopSCK` marking with `segMarkRK`. -/
@[expose] public noncomputable def segLoopSRK (c lo Wm1 seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkRK b (valueK (start.add i)) lo Wm1)

/-- `segMarkCK` with the mask built to the window's own width by `buildMaskNK`. -/
@[expose] public noncomputable def segMarkNK (seg p lo Wm1 n : Nat) : Nat :=
  clearHitK seg
    ((buildMaskNK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
      (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n).land seg)

/-- `segLoopSCK` marking with `segMarkNK`. -/
@[expose] public noncomputable def segLoopSNK (c lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkNK b (valueK (start.add i)) lo Wm1 n)

/-- One prime's mask joined into a running mask, leaving the window untouched. -/
@[expose] public noncomputable def segAccK (acc p lo Wm1 n : Nat) : Nat :=
  acc.lor (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
    (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n)

/-- The masks of a stretch of base primes joined into one, read from the slice `c` of the base
sieve. The window is cleared once against the result, in place of once per prime. -/
@[expose] public noncomputable def segAccLoopSK (c lo Wm1 n acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    (testBitK c i).rec a (segAccK a (valueK (start.add i)) lo Wm1 n)

/-- `segAccLoopSK` reading the base primes from the base sieve itself. -/
@[expose] public noncomputable def segAccLoopK (s lo Wm1 n acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    (testBitK s (start.add i)).rec a (segAccK a (valueK (start.add i)) lo Wm1 n)

/-- Loop recurrence for `segLoopCK`. -/
public theorem segLoopCK_succ {s lo Wm1 n seg start fuel : Nat} :
    segLoopCK s lo Wm1 n seg start (fuel + 1)
      = Bool.rec (segLoopCK s lo Wm1 n seg start fuel)
          (segMarkCK (segLoopCK s lo Wm1 n seg start fuel) (valueK (start + fuel)) lo Wm1 n)
          (testBitK s (start + fuel)) := rfl

/-- Fuel additivity for `segLoopCK`. -/
public theorem segLoopCK_add {s lo Wm1 n seg start a b : Nat} :
    segLoopCK s lo Wm1 n seg start (a + b)
      = segLoopCK s lo Wm1 n (segLoopCK s lo Wm1 n seg start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [segLoopCK_succ]

/-- One chain step for `segLoopCK`. -/
public theorem segLoopCK_chain {L s lo Wm1 n b b' start len rest : Nat}
    (hP : L = segLoopCK s lo Wm1 n b start (len.add rest))
    (h : (segLoopCK s lo Wm1 n b start len).beq b') :
    L = segLoopCK s lo Wm1 n b' (start.add len) rest := by
  grind [segLoopCK_add, Nat.beq_eq]

/-- Last chain step for `segLoopCK`. -/
public theorem segLoopCK_last {L s lo Wm1 n b b' start len : Nat}
    (hP : L = segLoopCK s lo Wm1 n b start len)
    (h : (segLoopCK s lo Wm1 n b start len).beq b') :
    L = b' := by
  grind [Nat.beq_eq]

/-! ### Joining two stretches of a run

The chain lemmas above move one batch at a time, so a run of `k` batches is a term nesting `k`
deep. These two join a pair of neighbouring stretches instead, so the emitter can combine batches
in a tree, each node its own declaration. -/

/-- A batch equation in `Eq` form. -/
public theorem segLoopK_of_beq {s lo Wm1 b b' start len : Nat}
    (h : (segLoopK s lo Wm1 b start len).beq b') : segLoopK s lo Wm1 b start len = b' :=
  Nat.beq_eq.mp h

/-- A clamped batch equation in `Eq` form. -/
public theorem segLoopCK_of_beq {s lo Wm1 n b b' start len : Nat}
    (h : (segLoopCK s lo Wm1 n b start len).beq b') : segLoopCK s lo Wm1 n b start len = b' :=
  Nat.beq_eq.mp h

/-- Two neighbouring stretches join into one. -/
public theorem segLoopK_join {s lo Wm1 b b' b'' start len rest : Nat}
    (h1 : segLoopK s lo Wm1 b start len = b')
    (h2 : segLoopK s lo Wm1 b' (start.add len) rest = b'') :
    segLoopK s lo Wm1 b start (len.add rest) = b'' := by
  rw [Nat.add_eq, segLoopK_add, h1]
  rwa [Nat.add_eq] at h2

/-- Two neighbouring clamped stretches join into one. -/
public theorem segLoopCK_join {s lo Wm1 n b b' b'' start len rest : Nat}
    (h1 : segLoopCK s lo Wm1 n b start len = b')
    (h2 : segLoopCK s lo Wm1 n b' (start.add len) rest = b'') :
    segLoopCK s lo Wm1 n b start (len.add rest) = b'' := by
  rw [Nat.add_eq, segLoopCK_add, h1]
  rwa [Nat.add_eq] at h2

/-! ### From the clamped marking back to `segMarkK`

`segMarkCK` drops seed bits above the window, runs `n` doubling rounds in place of 32, skips the
rounds entirely for a prime wider than the window, and leaves the window alone when nothing hits.
The lemmas below show it clears exactly the bits `segMarkK` clears, for any window below
`2 ^ (Wm1 + 1)`. -/

/-- `clearHitK` subtracts its second argument. -/
public theorem clearHitK_eq {seg hit : Nat} : clearHitK seg hit = seg - hit := by
  cases hit <;> rfl

/-- Two masks agreeing below `M` clear the same bits of a window below `2 ^ (M + 1)`. -/
public theorem land_congr_below {seg x y M : Nat} (hseg : seg < 2 ^ (M + 1))
    (h : ∀ i ≤ M, x.testBit i = y.testBit i) : seg.land x = seg.land y := by
  have hx : seg.land x = seg &&& x := rfl
  have hy : seg.land y = seg &&& y := rfl
  rw [hx, hy]
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [Nat.testBit_and]
  rcases Nat.lt_or_ge M i with hi | hi
  · have h2 : (2 : ℕ) ^ (M + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by lia) (by lia)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hseg h2)]
    simp
  · rw [h i hi]

/-- `seedK` in ordinary notation. -/
public theorem seedK_eq {A M : Nat} : seedK A M = if A ≤ M then 1 <<< A else 0 := by
  unfold seedK
  cases hb : Nat.ble A M with
  | true =>
    have h : A ≤ M := by grind [Nat.ble_eq]
    simp [h]
  | false =>
    have h : ¬ A ≤ M := by grind [Nat.ble_eq]
    simp [h]

/-- Below `M`, a clamped seed is the seed. -/
public theorem seedK_testBit {A M i : Nat} (hi : i ≤ M) :
    (seedK A M).testBit i = (1 <<< A : Nat).testBit i := by
  rw [seedK_eq]
  by_cases hA : A ≤ M
  · rw [if_pos hA]
  · rw [if_neg hA]
    have : A ≠ i := by lia
    simp [Nat.shiftLeft_eq, this]

/-- Both masks start from their two seeds. -/
public theorem buildMaskCK_zero {p M A B : Nat} :
    buildMaskCK p M A B 0 = seedK A M ||| seedK B M := rfl

/-- The mask starts from its two seeds. -/
public theorem buildMaskK_zero' {p M A B : Nat} :
    buildMaskK p M A B 0 = 1 <<< A ||| 1 <<< B := rfl

/-- Round recurrence for `buildMaskCK`, in the `Bool.rec` form the definition uses. -/
public theorem buildMaskCK_succ_raw {p M A B n : Nat} :
    buildMaskCK p M A B (n + 1)
      = Bool.rec (buildMaskCK p M A B n)
          ((buildMaskCK p M A B n).lor
            ((buildMaskCK p M A B n).shiftLeft (p.shiftLeft n.succ)))
          ((p.shiftLeft n.succ).ble M) := rfl

/-- Round recurrence for `buildMaskK`, in the `Bool.rec` form the definition uses. -/
public theorem buildMaskK_succ_raw' {p M A B n : Nat} :
    buildMaskK p M A B (n + 1)
      = Bool.rec (buildMaskK p M A B n)
          ((buildMaskK p M A B n).lor ((buildMaskK p M A B n).shiftLeft (p.shiftLeft n.succ)))
          ((p.shiftLeft n.succ).ble M) := rfl

/-- Round recurrence for `buildMaskCK`, in ordinary notation. -/
public theorem buildMaskCK_succ {p M A B n : Nat} :
    buildMaskCK p M A B (n + 1)
      = if p * 2 ^ (n + 1) ≤ M
        then buildMaskCK p M A B n ||| buildMaskCK p M A B n <<< (p * 2 ^ (n + 1))
        else buildMaskCK p M A B n := by
  have hs : p <<< (n + 1) = p * 2 ^ (n + 1) := by grind [Nat.shiftLeft_eq]
  simp [buildMaskCK_succ_raw, hs, Bool.rec_eq]

/-- Round recurrence for `buildMaskK`, in ordinary notation. -/
public theorem buildMaskK_succ' {p M A B n : Nat} :
    buildMaskK p M A B (n + 1)
      = if p * 2 ^ (n + 1) ≤ M
        then buildMaskK p M A B n ||| buildMaskK p M A B n <<< (p * 2 ^ (n + 1))
        else buildMaskK p M A B n := by
  have hs : p <<< (n + 1) = p * 2 ^ (n + 1) := by grind [Nat.shiftLeft_eq]
  simp [buildMaskK_succ_raw', hs, Bool.rec_eq]

/-- A prime wider than the window gets no rounds, whatever `n` says. -/
public theorem buildMaskCK_wide {p M A B n : Nat} (hw : M < p * 2) :
    buildMaskCK p M A B n = buildMaskCK p M A B 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [buildMaskCK_succ, ih]
    have hle : p * 2 ≤ p * 2 ^ (n + 1) := by
      have h2 : (2 : Nat) ≤ 2 ^ (n + 1) := Nat.one_lt_two_pow (by lia)
      exact Nat.mul_le_mul_left p h2
    rw [if_neg (by lia)]

/-- Below `M`, the clamped mask is the mask. -/
public theorem buildMaskCK_testBit {p M A B n : Nat} :
    ∀ i ≤ M, (buildMaskCK p M A B n).testBit i = (buildMaskK p M A B n).testBit i := by
  induction n with
  | zero =>
    intro i hi
    rw [buildMaskCK_zero, buildMaskK_zero', Nat.testBit_or, Nat.testBit_or, seedK_testBit hi,
      seedK_testBit hi]
  | succ n ih =>
    intro i hi
    rw [buildMaskCK_succ, buildMaskK_succ']
    by_cases hc : p * 2 ^ (n + 1) ≤ M
    · rw [if_pos hc, if_pos hc, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.testBit_shiftLeft, ih i hi]
      rcases Nat.lt_or_ge i (p * 2 ^ (n + 1)) with hlt | hge
      · simp [Nat.not_le_of_lt hlt]
      · rw [ih (i - p * 2 ^ (n + 1)) (by lia)]
    · rw [if_neg hc, if_neg hc]
      exact ih i hi

/-- Rounds past the width of the window change nothing. -/
public theorem buildMaskK_rounds {p M A B n : Nat} (hp : 1 ≤ p) (hM : M < 2 ^ n) :
    ∀ m, n ≤ m → buildMaskK p M A B m = buildMaskK p M A B n := by
  intro m
  induction m with
  | zero => intro h; grind
  | succ m ih =>
    intro h
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm : n ≤ m := by lia
      have h1 : (2 : ℕ) ^ n ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by lia) (by lia)
      have h3 : 1 * 2 ^ (m + 1) ≤ p * 2 ^ (m + 1) := Nat.mul_le_mul_right _ hp
      have hbig : ¬ (p * 2 ^ (m + 1) ≤ M) := by lia
      rw [buildMaskK_succ', if_neg hbig]
      exact ih hnm
    · have hnm : n = m + 1 := by lia
      rw [hnm]

/-- For a prime wider than the window, every round is a no-op. -/
public theorem buildMaskK_rounds_wide {p M A B : Nat} (hw : M < p * 2) :
    ∀ m, buildMaskK p M A B m = buildMaskK p M A B 0 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : p * 2 ≤ p * 2 ^ (m + 1) := by
      have : (2 : ℕ) ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by lia) (by lia)
      have h2 : p * 2 ^ 1 ≤ p * 2 ^ (m + 1) := Nat.mul_le_mul_left _ this
      lia
    rw [buildMaskK_succ', if_neg (by lia)]
    exact ih

/-- A window never grows as the loop runs. -/
public theorem segLoopK_le {s lo Wm1 seg start fuel : Nat} :
    segLoopK s lo Wm1 seg start fuel ≤ seg := by
  induction fuel with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [segLoopK_succ]
    cases testBitK s (start + n) with
    | false => exact ih
    | true => exact Nat.le_trans (Nat.sub_le _ _) ih

/-- Every position names a positive number. -/
public theorem one_le_valueK {k : Nat} : 1 ≤ valueK k := by
  unfold valueK
  lia

/-- The clamped marking removes the prime's mask from the window. -/
public theorem segMarkCK_ldiff {seg p lo Wm1 n : Nat} :
    segMarkCK seg p lo Wm1 n
      = Nat.ldiff seg (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n) := by
  have hite : segMarkCK seg p lo Wm1 n
      = if p * 2 ≤ Wm1
        then clearHitK seg ((buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n).land seg)
        else clearHitK seg ((buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 0).land seg) := by
    simp [segMarkCK, Bool.rec_eq, Nat.ble_eq, Nat.mul_eq, buildMaskCK_zero]
  have hland : ∀ m : Nat, Nat.ldiff seg m = seg - m.land seg := by
    intro m
    have h1 : m.land seg = seg &&& m := Nat.land_comm m seg
    rw [h1, Nat.sub_and_eq_ldiff]
  rw [hite, hland]
  by_cases hc : p * 2 ≤ Wm1
  · rw [if_pos hc, clearHitK_eq]
  · have hwide : buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
        (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n
        = buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 0 := buildMaskCK_wide (by lia)
    rw [if_neg hc, clearHitK_eq, hwide]

/-- Removing a mask, written with the two operations the kernel reduces directly. -/
public theorem ldiff_eq_sub {seg m : Nat} : Nat.ldiff seg m = Nat.sub seg (Nat.land m seg) := by
  have h1 : Nat.land m seg = seg &&& m := Nat.land_comm m seg
  have h2 : Nat.sub seg (seg &&& m) = seg - (seg &&& m) := rfl
  rw [h1, h2, Nat.sub_and_eq_ldiff]

/-- Removing two masks one after the other removes their union. -/
public theorem ldiff_ldiff {seg m1 m2 : Nat} :
    Nat.ldiff (Nat.ldiff seg m1) m2 = Nat.ldiff seg (m1 ||| m2) := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp [Nat.testBit_ldiff, Nat.testBit_or, Bool.and_assoc]

/-- The clamped marking clears exactly the bits the marking clears, for a window inside the
range. -/
public theorem segMarkCK_eq {seg p lo Wm1 n : Nat} (hseg : seg < 2 ^ (Wm1 + 1)) (hp : 1 ≤ p)
    (hn : Wm1 < 2 ^ n) (hn32 : n ≤ 32) :
    segMarkCK seg p lo Wm1 n = segMarkK seg p lo Wm1 := by
  have hite : segMarkCK seg p lo Wm1 n
      = if p * 2 ≤ Wm1
        then clearHitK seg (seg.land (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n))
        else clearHitK seg (seg.land
          ((seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
            (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1))) := by
    simp [segMarkCK, Bool.rec_eq, Nat.ble_eq, Nat.mul_eq, Nat.land_comm]
  have hsub : ∀ x : Nat, seg.sub x = seg - x := fun _ => rfl
  rw [hite, segMarkK, hsub]
  by_cases hc : p * 2 ≤ Wm1
  · rw [if_pos hc, clearHitK_eq, buildMaskK_rounds hp hn 32 hn32,
      land_congr_below hseg fun i hi => buildMaskCK_testBit i hi]
  · have hw : Wm1 < p * 2 := by lia
    have hseed : (seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
        (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1)
        = buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 0 := rfl
    rw [if_neg hc, clearHitK_eq, hseed, buildMaskK_rounds_wide hw 32,
      land_congr_below hseg fun i hi => buildMaskCK_testBit i hi]

/-- Loop recurrence for `segLoopCK`, with the window bound carried along. -/
public theorem segLoopCK_eq {s lo Wm1 n seg start fuel : Nat} (hseg : seg < 2 ^ (Wm1 + 1))
    (hn : Wm1 < 2 ^ n) (hn32 : n ≤ 32) :
    segLoopCK s lo Wm1 n seg start fuel = segLoopK s lo Wm1 seg start fuel := by
  induction fuel with
  | zero => rfl
  | succ m ih =>
    rw [segLoopCK_succ, segLoopK_succ, ih]
    cases testBitK s (start + m) with
    | false => rfl
    | true =>
      exact segMarkCK_eq (Nat.lt_of_le_of_lt segLoopK_le hseg) one_le_valueK hn hn32

/-- The window a run starts from is inside the range. -/
public theorem initSegK_lt {W : Nat} : initSegK W < 2 ^ W := by
  unfold initSegK
  have hs : Nat.shiftLeft 1 W = 1 <<< W := rfl
  have h : (1 : Nat) <<< W = 2 ^ W := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hpos : 0 < 2 ^ W := Nat.two_pow_pos W
  rw [hs, h]
  lia

/-- Loop recurrence for `segLoopSCK`. -/
public theorem segLoopSCK_succ {c lo Wm1 n seg start fuel : Nat} :
    segLoopSCK c lo Wm1 n seg start (fuel + 1)
      = Bool.rec (segLoopSCK c lo Wm1 n seg start fuel)
          (segMarkCK (segLoopSCK c lo Wm1 n seg start fuel) (valueK (start + fuel)) lo Wm1 n)
          (testBitK c fuel) := rfl

/-- Loop recurrence for `segAccLoopSK`. -/
public theorem segAccLoopSK_succ {c lo Wm1 n acc start fuel : Nat} :
    segAccLoopSK c lo Wm1 n acc start (fuel + 1)
      = Bool.rec (segAccLoopSK c lo Wm1 n acc start fuel)
          (segAccK (segAccLoopSK c lo Wm1 n acc start fuel) (valueK (start + fuel)) lo Wm1 n)
          (testBitK c fuel) := rfl

/-- A joining step in ordinary notation, with the new mask first. -/
public theorem segAccK_eq {acc p lo Wm1 n : Nat} :
    segAccK acc p lo Wm1 n
      = buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n ||| acc := by
  unfold segAccK
  have hor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  rw [hor, Nat.lor_comm]

/-- Anything joined into the accumulator before a batch can be joined after it instead. -/
public theorem segAccLoopSK_lor {c lo Wm1 n x acc start fuel : Nat} :
    segAccLoopSK c lo Wm1 n (x ||| acc) start fuel
      = x ||| segAccLoopSK c lo Wm1 n acc start fuel := by
  induction fuel with
  | zero => rfl
  | succ m ih =>
    rw [segAccLoopSK_succ, segAccLoopSK_succ]
    cases testBitK c m with
    | false => exact ih
    | true =>
      simp only [segAccK_eq, ih]
      rw [← Nat.lor_assoc, ← Nat.lor_assoc, Nat.lor_comm (buildMaskCK _ _ _ _ _) x]

/-- Loop recurrence for `segAccLoopK`. -/
public theorem segAccLoopK_succ {s lo Wm1 n acc start fuel : Nat} :
    segAccLoopK s lo Wm1 n acc start (fuel + 1)
      = Bool.rec (segAccLoopK s lo Wm1 n acc start fuel)
          (segAccK (segAccLoopK s lo Wm1 n acc start fuel) (valueK (start + fuel)) lo Wm1 n)
          (testBitK s (start + fuel)) := rfl

/-- Fuel additivity for `segAccLoopK`. -/
public theorem segAccLoopK_add {s lo Wm1 n acc start a b : Nat} :
    segAccLoopK s lo Wm1 n acc start (a + b)
      = segAccLoopK s lo Wm1 n (segAccLoopK s lo Wm1 n acc start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [segAccLoopK_succ]

/-- One chain step for `segAccLoopK`. -/
public theorem segAccLoopK_chain {L s lo Wm1 n acc acc' start len rest : Nat}
    (hP : L = segAccLoopK s lo Wm1 n acc start (len.add rest))
    (h : (segAccLoopK s lo Wm1 n acc start len).beq acc') :
    L = segAccLoopK s lo Wm1 n acc' (start.add len) rest := by
  grind [segAccLoopK_add, Nat.beq_eq]

/-- Last chain step for `segAccLoopK`. -/
public theorem segAccLoopK_last {L s lo Wm1 n acc acc' start len : Nat}
    (hP : L = segAccLoopK s lo Wm1 n acc start len)
    (h : (segAccLoopK s lo Wm1 n acc start len).beq acc') : L = acc' := by
  grind [Nat.beq_eq]

/-- A slice agreeing with the base sieve on the batch's positions joins the same masks. -/
public theorem segAccLoopSK_eq {c s lo Wm1 n acc start len : Nat}
    (h : ∀ i < len, testBitK c i = testBitK s (start + i)) :
    segAccLoopSK c lo Wm1 n acc start len = segAccLoopK s lo Wm1 n acc start len := by
  induction len with
  | zero => rfl
  | succ m ih =>
    rw [segAccLoopSK_succ, segAccLoopK_succ, ih fun i hi => h i (by lia), h m (by lia)]

/-- Anything joined into the accumulator before a run can be joined after it instead. -/
public theorem segAccLoopK_lor {s lo Wm1 n x acc start fuel : Nat} :
    segAccLoopK s lo Wm1 n (x ||| acc) start fuel
      = x ||| segAccLoopK s lo Wm1 n acc start fuel := by
  induction fuel with
  | zero => rfl
  | succ m ih =>
    rw [segAccLoopK_succ, segAccLoopK_succ]
    cases testBitK s (start + m) with
    | false => exact ih
    | true =>
      simp only [segAccK_eq, ih]
      rw [← Nat.lor_assoc, ← Nat.lor_assoc, Nat.lor_comm (buildMaskCK _ _ _ _ _) x]

/-- A run's accumulator splits into the run's own masks and whatever it started from. -/
public theorem segAccLoopK_zero {s lo Wm1 n acc start fuel : Nat} :
    segAccLoopK s lo Wm1 n acc start fuel = segAccLoopK s lo Wm1 n 0 start fuel ||| acc := by
  have h := segAccLoopK_lor (s := s) (lo := lo) (Wm1 := Wm1) (n := n) (x := acc) (acc := 0)
    (start := start) (fuel := fuel)
  have hz : acc ||| 0 = acc := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  rw [hz] at h
  rw [h, Nat.lor_comm]

/-- A batch's accumulator splits into the batch's own masks and whatever it started from. -/
public theorem segAccLoopSK_zero {c lo Wm1 n acc start fuel : Nat} :
    segAccLoopSK c lo Wm1 n acc start fuel = segAccLoopSK c lo Wm1 n 0 start fuel ||| acc := by
  have h := segAccLoopSK_lor (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (x := acc) (acc := 0)
    (start := start) (fuel := fuel)
  have hz : acc ||| 0 = acc := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  rw [hz] at h
  rw [h, Nat.lor_comm]

/-- Clearing the window once against the joined masks of a batch gives what clearing it once per
prime gives. -/
public theorem segLoopSCK_eq_ldiff {c lo Wm1 n seg acc start fuel : Nat} :
    Nat.ldiff (segLoopSCK c lo Wm1 n seg start fuel) acc
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n acc start fuel) := by
  induction fuel generalizing acc with
  | zero => rfl
  | succ m ih =>
    rw [segLoopSCK_succ, segAccLoopSK_succ]
    cases testBitK c m with
    | false => exact ih
    | true =>
      simp only [segMarkCK_ldiff, segAccK_eq, ldiff_ldiff, ih]
      refine congrArg (Nat.ldiff seg) ?_
      rw [segAccLoopSK_zero, segAccLoopSK_zero (acc := acc)]
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_or]
      grind

/-- The same, over the base sieve itself: a whole run clears the window once against the joined
masks of every prime it passes. -/
public theorem segLoopCK_eq_ldiff {s lo Wm1 n seg acc start fuel : Nat} :
    Nat.ldiff (segLoopCK s lo Wm1 n seg start fuel) acc
      = Nat.ldiff seg (segAccLoopK s lo Wm1 n acc start fuel) := by
  induction fuel generalizing acc with
  | zero => rfl
  | succ m ih =>
    rw [segLoopCK_succ, segAccLoopK_succ]
    cases testBitK s (start + m) with
    | false => exact ih
    | true =>
      simp only [segMarkCK_ldiff, segAccK_eq, ldiff_ldiff, ih]
      refine congrArg (Nat.ldiff seg) ?_
      rw [segAccLoopK_zero, segAccLoopK_zero (acc := acc)]
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_or]
      grind

/-- A run of a whole window is the window with every mask removed at once. -/
public theorem segLoopCK_ldiff_total {s lo Wm1 n seg start fuel : Nat} :
    segLoopCK s lo Wm1 n seg start fuel
      = Nat.ldiff seg (segAccLoopK s lo Wm1 n 0 start fuel) := by
  have h := segLoopCK_eq_ldiff (s := s) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg) (acc := 0)
    (start := start) (fuel := fuel)
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  rwa [hz] at h

/-- A slice agreeing with the base sieve on the batch's positions runs the clamped batch the same
way. -/
public theorem segLoopSCK_eq {c s lo Wm1 n seg start len : Nat}
    (h : ∀ i < len, testBitK c i = testBitK s (start + i)) :
    segLoopSCK c lo Wm1 n seg start len = segLoopCK s lo Wm1 n seg start len := by
  induction len with
  | zero => rfl
  | succ m ih =>
    rw [segLoopSCK_succ, segLoopCK_succ, ih fun i hi => h i (by lia), h m (by lia)]

/-- A clamped run of a whole window gives the value the plain run gives, with the three side
conditions as Boolean tests the kernel settles. -/
public theorem segEq_of_clamped {s lo W Wm1 n fuel b : Nat} (hW : (Wm1 + 1).beq W)
    (hn : Nat.blt Wm1 (2 ^ n)) (hn32 : Nat.ble n 32)
    (h : segLoopCK s lo Wm1 n (initSegK W) 1 fuel = b) :
    segLoopK s lo Wm1 (initSegK W) 1 fuel = b := by
  have hw : Wm1 + 1 = W := by grind [Nat.beq_eq]
  have h1 : initSegK W < 2 ^ (Wm1 + 1) := by rw [hw]; exact initSegK_lt
  have h2 : Wm1 < 2 ^ n := by grind [Nat.blt_eq]
  have h3 : n ≤ 32 := by grind [Nat.ble_eq]
  rw [← segLoopCK_eq h1 h2 h3]
  exact h

/-! ### From a slice of the base sieve back to the base sieve

`segLoopSK` reads a slice, so a batch equation about it says nothing about the base sieve until
the slice is tied back. The two lemmas below do that: a slice agreeing with the base sieve on the
batch's positions gives the same run, and the slice the emitter uses does agree. -/

/-- Loop recurrence for `segLoopSK`. -/
public theorem segLoopSK_succ {c lo Wm1 seg start fuel : Nat} :
    segLoopSK c lo Wm1 seg start (fuel + 1)
      = Bool.rec (segLoopSK c lo Wm1 seg start fuel)
          (segMarkK (segLoopSK c lo Wm1 seg start fuel) (valueK (start + fuel)) lo Wm1)
          (testBitK c fuel) := rfl

/-- A slice that agrees with the base sieve on the batch's positions runs the batch the same way. -/
public theorem segLoopSK_eq {c s lo Wm1 seg start len : Nat}
    (h : ∀ i < len, testBitK c i = testBitK s (start + i)) :
    segLoopSK c lo Wm1 seg start len = segLoopK s lo Wm1 seg start len := by
  induction len with
  | zero => rfl
  | succ n ih =>
    rw [segLoopSK_succ, segLoopK_succ, ih fun i hi => h i (by lia), h n (by lia)]

/-- The slice `(s >>> start) &&& (2 ^ len - 1)` agrees with `s` on the batch's positions. -/
public theorem testBitK_slice {s start len i : Nat} (hi : i < len) :
    testBitK (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)) i
      = testBitK s (start + i) := by
  simp [testBitK_eq_testBit, Nat.shiftLeft_eq, Nat.testBit_shiftRight, hi]

/-- One chain step from a slice batch: the slice equation and the batch equation together move the
run forward by `len` steps of the base sieve. -/
public theorem segLoopSK_chain {L s lo Wm1 b b' c start len rest : Nat}
    (hP : L = segLoopK s lo Wm1 b start (len.add rest))
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSK c lo Wm1 b start len).beq b') :
    L = segLoopK s lo Wm1 b' (start.add len) rest := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSK_eq fun i hi => testBitK_slice hi] at h
  exact segLoopK_chain hP h

/-- Last chain step from a slice batch. -/
public theorem segLoopSK_last {L s lo Wm1 b b' c start len : Nat}
    (hP : L = segLoopK s lo Wm1 b start len)
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSK c lo Wm1 b start len).beq b') :
    L = b' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSK_eq fun i hi => testBitK_slice hi] at h
  exact segLoopK_last hP h

/-- A slice batch as a standalone equation about the base sieve, for the join tree. -/
public theorem segLoopSK_leaf {s lo Wm1 b b' c start len : Nat}
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSK c lo Wm1 b start len).beq b') :
    segLoopK s lo Wm1 b start len = b' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSK_eq fun i hi => testBitK_slice hi] at h
  exact Nat.beq_eq.mp h

/-- A clamped slice batch as a standalone equation, for the join tree. -/
public theorem segLoopSCK_leaf {s lo Wm1 n b b' c start len : Nat}
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSCK c lo Wm1 n b start len).beq b') :
    segLoopCK s lo Wm1 n b start len = b' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSCK_eq fun i hi => testBitK_slice hi] at h
  exact Nat.beq_eq.mp h

/-- A batch of joined masks as a standalone equation about the base sieve. -/
public theorem segAccLoopSK_leaf {s lo Wm1 n acc acc' c start len : Nat}
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segAccLoopSK c lo Wm1 n acc start len).beq acc') :
    segAccLoopK s lo Wm1 n acc start len = acc' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segAccLoopSK_eq fun i hi => testBitK_slice hi] at h
  exact Nat.beq_eq.mp h

/-- Two neighbouring stretches of joined masks join into one. -/
public theorem segAccLoopK_join {s lo Wm1 n acc acc' acc'' start len rest : Nat}
    (h1 : segAccLoopK s lo Wm1 n acc start len = acc')
    (h2 : segAccLoopK s lo Wm1 n acc' (start.add len) rest = acc'') :
    segAccLoopK s lo Wm1 n acc start (len.add rest) = acc'' := by
  rw [Nat.add_eq, segAccLoopK_add, h1]
  rwa [Nat.add_eq] at h2

/-- The window with every joined mask removed at once, as the run's value. -/
public theorem segLoopCK_of_acc {s lo Wm1 W n acc bits fuel : Nat}
    (hacc : segAccLoopK s lo Wm1 n 0 1 fuel = acc)
    (hb : (Nat.sub (initSegK W) (Nat.land acc (initSegK W))).beq bits) :
    segLoopCK s lo Wm1 n (initSegK W) 1 fuel = bits := by
  rw [segLoopCK_ldiff_total, hacc, ldiff_eq_sub]
  exact Nat.beq_eq.mp hb

/-- One chain step from a clamped slice batch. -/
public theorem segLoopSCK_chain {L s lo Wm1 n b b' c start len rest : Nat}
    (hP : L = segLoopCK s lo Wm1 n b start (len.add rest))
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSCK c lo Wm1 n b start len).beq b') :
    L = segLoopCK s lo Wm1 n b' (start.add len) rest := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSCK_eq fun i hi => testBitK_slice hi] at h
  exact segLoopCK_chain hP h

/-- Last chain step from a clamped slice batch. -/
public theorem segLoopSCK_last {L s lo Wm1 n b b' c start len : Nat}
    (hP : L = segLoopCK s lo Wm1 n b start len)
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSCK c lo Wm1 n b start len).beq b') :
    L = b' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSCK_eq fun i hi => testBitK_slice hi] at h
  exact segLoopCK_last hP h

/-! ## What the window holds

The two facts below are the arithmetic that segmentation actually adds: the local seed is the
right one, and a local offset names the number you expect. -/

/-- `firstLocK` in ordinary notation, for use in proofs. -/
public theorem firstLocK_eq {A lo m : ℕ} :
    firstLocK A lo m = (A + m * (lo / m + 1) - lo) % m := rfl

/-- The seed offset lies inside one period. -/
public theorem firstLocK_lt {A lo m : ℕ} (hm : 0 < m) : firstLocK A lo m < m := by
  rw [firstLocK_eq]
  exact Nat.mod_lt _ hm

/-- The seed offset puts the window position `lo + firstLocK A lo m` in the progression
`A, A + m, A + 2*m, …`, which is the hypothesis shape the `buildMaskK` bit characterisation in
`PrimeCert.SieveCorrect` asks for. Needs `A ≤ lo`: the window sits above the base range. -/
public theorem firstLocK_spec {A lo m : ℕ} (hm : 0 < m) (hA : A ≤ lo) :
    ∃ c, lo + firstLocK A lo m = A + m * c := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = A + m - lo % m := ⟨_, rfl⟩
  have h2 : m * (lo / m) + lo % m = lo := Nat.div_add_mod lo m
  have h3 : lo % m < m := Nat.mod_lt _ hm
  have h1 : m * (lo / m + 1) = m * (lo / m) + m := Nat.mul_succ _ _
  have h4 : m * (x / m) + x % m = x := Nat.div_add_mod x m
  have hx : firstLocK A lo m = x % m := by
    rw [firstLocK_eq, hxdef]
    congr 1
    lia
  have h5 : x / m ≤ lo / m + 1 := by
    have hle : m * (x / m) ≤ m * (lo / m + 1) := by lia
    exact Nat.le_of_mul_le_mul_left hle hm
  obtain ⟨c, hc⟩ : ∃ c, lo / m + 1 = x / m + c := ⟨lo / m + 1 - x / m, by lia⟩
  have h8 : m * (lo / m + 1) = m * (x / m + c) := by rw [hc]
  have h7 : m * (x / m + c) = m * (x / m) + m * c := Nat.left_distrib _ _ _
  exact ⟨c, by rw [hx]; lia⟩

/-- The number at local offset `2*k` of a window starting at `a`. -/
public theorem value_index_add {a k : ℕ} (ha : a % 6 = 1 ∨ a % 6 = 5) :
    value (index a + 2 * k) = a + 6 * k := by
  grind [value, index]

/-- The completed run over the window of `W` positions from `a`, sieved by the base primes up to
`B`, in terms of `a`, `W` and `B` themselves. This is the form the correctness statements speak in
and the form `run_segment` emits alongside the numeral one, through `segRun_of`. -/
@[expose] public noncomputable def segRun (s a W B : ℕ) : ℕ :=
  segLoopK s (index a) (W - 1) (initSegK W) 1 (index B)

/-- `segRun` in the raw form the batch lemmas chain to. -/
public theorem segRun_eq {s a W B : ℕ} :
    segRun s a W B = segLoopK s (index a) (W - 1) (initSegK W) 1 (index B) := rfl

/-- The numeral form the batches produce carries over to `segRun`, given that the numerals are the
ones `a`, `W` and `B` compute to. -/
public theorem segRun_of {s a lo W wm1 B fuel b : ℕ} (hlo : Nat.beq (indexK a) lo = true)
    (hw : Nat.beq (Nat.sub W 1) wm1 = true) (hf : Nat.beq (indexK B) fuel = true)
    (h : segLoopK s lo wm1 (initSegK W) 1 fuel = b) : segRun s a W B = b := by
  have h1 : index a = lo := by
    have hb := Nat.eq_of_beq_eq_true hlo
    rwa [indexK_eq_index] at hb
  have h2 : W - 1 = wm1 := Nat.eq_of_beq_eq_true hw
  have h3 : index B = fuel := by
    have hb := Nat.eq_of_beq_eq_true hf
    rwa [indexK_eq_index] at hb
  rw [segRun_eq, h1, h2, h3]
  exact h

/-- Every surviving bit of the window names a number with no prime factor among the base primes,
proved by `segmentSound_of`. One direction only: a cleared bit is left unclassified, so this gives
primality of the survivors exactly when the window sits below the square of the base bound. -/
@[expose] public def SegmentSound (s B a W : ℕ) : Prop :=
  ∀ j < W, (segLoopK s (index a) (W - 1) (initSegK W) 1 (index B)).testBit j →
    ∀ q ≤ B, q.Prime → ¬ q ∣ value (index a + j)

/-! ## Correctness of a segment

A surviving bit names a number with no prime factor among the base primes. The argument: for a
prime `q` dividing the number at position `j`, the run reaches `q`'s own base index with `q`'s bit
set in the base sieve, the mask built there covers `j`, and every later step only clears bits. -/

/-- A step clears exactly the bits of the mask. -/
public theorem testBit_segMarkK {seg p lo Wm1 j : Nat} :
    (segMarkK seg p lo Wm1).testBit j
      = (seg.testBit j && !(buildMaskK p Wm1 (firstLocK (indexK (p * 5)) lo (p * 2))
          (firstLocK (indexK (p * 7)) lo (p * 2)) 32).testBit j) := by
  have hraw : segMarkK seg p lo Wm1
      = seg - (seg &&& buildMaskK p Wm1 (firstLocK (indexK (p * 5)) lo (p * 2))
          (firstLocK (indexK (p * 7)) lo (p * 2)) 32) := rfl
  rw [hraw, Nat.sub_and_eq_ldiff, Nat.testBit_ldiff]

/-- A run only clears bits: a bit set at the end was set at the start. -/
public theorem testBit_of_testBit_segLoopK {s lo Wm1 seg start fuel j : Nat}
    (h : (segLoopK s lo Wm1 seg start fuel).testBit j) : seg.testBit j := by
  induction fuel with
  | zero => exact h
  | succ n ih =>
    rw [segLoopK_succ] at h
    cases hb : testBitK s (start + n) with
    | false =>
      rw [hb] at h
      exact ih h
    | true =>
      rw [hb, testBit_segMarkK, Bool.and_eq_true] at h
      exact ih h.1

/-- The offset of a multiple of `p` inside the window lies in one of the two progressions the mask
draws, so the mask covers it. -/
public theorem testBit_mask_of_dvd {q lo j c X : Nat} (hq : 0 < q)
    (hX : X ≤ lo) (hstep : lo + j = X + 2 * q * c) :
    firstLocK X lo (q * 2) ≤ j ∧ 2 * q ∣ j - firstLocK X lo (q * 2) := by
  have hm : 0 < q * 2 := by lia
  obtain ⟨c0, hc0⟩ := firstLocK_spec (A := X) (lo := lo) hm hX
  have hA : firstLocK X lo (q * 2) < q * 2 := firstLocK_lt hm
  have hcc : c0 ≤ c := by
    by_contra hlt
    have h1 : c + 1 ≤ c0 := by lia
    have h2 : q * 2 * (c + 1) ≤ q * 2 * c0 := Nat.mul_le_mul_left _ h1
    have h3 : q * 2 * (c + 1) = q * 2 * c + q * 2 := by rw [Nat.mul_add, Nat.mul_one]
    lia
  have hsplit : q * 2 * c = q * 2 * c0 + q * 2 * (c - c0) := by
    rw [← Nat.mul_add]
    congr 1
    lia
  exact ⟨by lia, ⟨c - c0, by lia⟩⟩

/-- A run that passes an index whose base bit is set, with a mask covering `j`, leaves bit `j`
clear. -/
public theorem not_testBit_segLoopK {s lo Wm1 seg start fuel t j : Nat}
    (htf : t < start + fuel) (hts : start ≤ t) (hbit : testBitK s t = true)
    (hmask : (buildMaskK (valueK t) Wm1 (firstLocK (indexK (valueK t * 5)) lo (valueK t * 2))
      (firstLocK (indexK (valueK t * 7)) lo (valueK t * 2)) 32).testBit j = true) :
    (segLoopK s lo Wm1 seg start fuel).testBit j = false := by
  induction fuel with
  | zero => lia
  | succ n ih =>
    rw [segLoopK_succ]
    cases hb : testBitK s (start + n) with
    | false =>
      refine ih ?_
      rcases Nat.lt_or_ge t (start + n) with hlt | hge
      · exact hlt
      · have ht : start + n = t := by lia
        rw [ht, hbit] at hb
        exact absurd hb (by simp)
    | true =>
      rw [testBit_segMarkK]
      rcases Nat.lt_or_ge t (start + n) with hlt | hge
      · rw [ih hlt]
        simp
      · have ht : start + n = t := by lia
        rw [ht, hmask]
        simp

set_option maxHeartbeats 1000000 in
-- The proof carries a dozen arithmetic side conditions about `index`, `value` and divisibility,
-- each closed by `lia` against the whole context, which together pass the default limit.
/-- Every surviving bit of a completed run names a number with no prime factor up to `B`. -/
public theorem segmentSound_of {s B a W : Nat} (hs : IsSieve B s)
    (ha : a % 6 = 1 ∨ a % 6 = 5) (hW : W - 1 < 2 ^ 32) (hB1 : 1 ≤ B) (h7B : 7 * B ≤ a) :
    SegmentSound s B a W := by
  intro j hj hbit q hqB hq hdvd
  have hlo : value (index a) = a := value_index ha
  have hjval : a ≤ value (index a + j) := by
    have := value_strictMono.monotone (Nat.le_add_right (index a) j)
    lia
  have hcop : Nat.Coprime (value (index a + j)) 6 := value_coprime6
  have hqcop : Nat.Coprime q 6 := Nat.Coprime.coprime_dvd_left hdvd hcop
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 := coprime6_mod.mp hqcop
  have hq2 : 2 ≤ q := hq.two_le
  have hq5 : 5 ≤ q := by lia
  obtain ⟨k, hk⟩ := hdvd
  have hkcop : Nat.Coprime k 6 := Nat.Coprime.coprime_dvd_left ⟨q, by lia⟩ hcop
  have hk6 : k % 6 = 1 ∨ k % 6 = 5 := coprime6_mod.mp hkcop
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have h1 : k ≤ 1 := by lia
    have h2 : q * k ≤ q * 1 := Nat.mul_le_mul_left q h1
    lia
  have hk5 : 5 ≤ k := by lia
  -- the base index of `q`, and its bit in the base sieve
  have hvq : value (index q) = q := value_index hq6
  have ht0 : index q ≠ 0 := by
    unfold index
    lia
  have htB : index q ≤ index B := by
    unfold index
    lia
  have hbitq : s.testBit (index q) := by
    have hle : value (index q) ≤ B := by lia
    have hpr : (value (index q)).Prime := by rwa [hvq]
    exact (hs (index q) ht0 hle).mpr hpr
  -- the mask built at `q` covers `j`
  have hmask : (buildMaskK q (W - 1) (firstLocK (indexK (q * 5)) (index a) (q * 2))
      (firstLocK (indexK (q * 7)) (index a) (q * 2)) 32).testBit j := by
    rw [testBit_buildMaskK (by lia) (by lia) hW]
    rcases hk6 with h1 | h5
    · right
      obtain ⟨c, rfl⟩ : ∃ c, k = 7 + 6 * c := ⟨(k - 7) / 6, by lia⟩
      have hval : value (index a + j) = value (index (q * 7)) + 6 * (q * c) := by
        rw [value_startB hq6]
        lia
      have hstep : index a + j = index (q * 7) + 2 * q * c := by
        have := value_add_two_mul (k := index (q * 7)) (m := q * c)
        have heq : value (index a + j) = value (index (q * 7) + 2 * (q * c)) := by lia
        have := value_strictMono.injective heq
        lia
      have h7q : q * 7 ≤ B * 7 := Nat.mul_le_mul_right 7 hqB
      have hX : index (q * 7) ≤ index a := by
        unfold index
        lia
      simpa using testBit_mask_of_dvd (q := q) (by lia) hX hstep
    · left
      obtain ⟨c, rfl⟩ : ∃ c, k = 5 + 6 * c := ⟨(k - 5) / 6, by lia⟩
      have hval : value (index a + j) = value (index (q * 5)) + 6 * (q * c) := by
        rw [value_startA hq6]
        lia
      have hstep : index a + j = index (q * 5) + 2 * q * c := by
        have := value_add_two_mul (k := index (q * 5)) (m := q * c)
        have heq : value (index a + j) = value (index (q * 5) + 2 * (q * c)) := by lia
        have := value_strictMono.injective heq
        lia
      have h5q : q * 5 ≤ B * 7 := by
        have := Nat.mul_le_mul_right 5 hqB
        lia
      have hX : index (q * 5) ≤ index a := by
        unfold index
        lia
      simpa using testBit_mask_of_dvd (q := q) (by lia) hX hstep
  -- the run passes `q`'s index, so the bit is clear at the end
  have hbitK : testBitK s (index q) = true := by
    rw [testBitK_eq_testBit]
    exact hbitq
  have hmaskK : (buildMaskK (valueK (index q)) (W - 1)
      (firstLocK (indexK (valueK (index q) * 5)) (index a) (valueK (index q) * 2))
      (firstLocK (indexK (valueK (index q) * 7)) (index a) (valueK (index q) * 2)) 32).testBit j
      = true := by
    rw [valueK_eq_value, hvq, indexK_eq_index]
    exact hmask
  have hclear := not_testBit_segLoopK (s := s) (lo := index a) (Wm1 := W - 1)
    (seg := initSegK W) (start := 1) (fuel := index B) (t := index q) (j := j)
    (by lia) (by lia) hbitK hmaskK
  rw [hclear] at hbit
  exact absurd hbit (by simp)

/-! ## Completeness of a segment

The converse direction: a cleared bit is cleared for a reason. Each step clears only the mask of
one base prime, and a mask bit of `p` sits at an offset whose number is a multiple of `p`, so a
number with no prime factor up to `B` keeps its bit through the whole run. -/

/-- A mask bit of `p` in the window names a multiple of `p`. -/
public theorem dvd_of_testBit_mask {p lo Wm1 j : Nat} (hp6 : p % 6 = 1 ∨ p % 6 = 5)
    (hp5 : 5 ≤ p) (hlo : index (p * 7) ≤ lo) (hj : j ≤ Wm1) (hW : Wm1 < 2 ^ 32)
    (h : (buildMaskK p Wm1 (firstLocK (index (p * 5)) lo (p * 2))
      (firstLocK (index (p * 7)) lo (p * 2)) 32).testBit j = true) :
    p ∣ value (lo + j) := by
  have hm : 0 < p * 2 := by lia
  have h57 : index (p * 5) ≤ index (p * 7) := by
    unfold index
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (by lia) 1)
  have h5lo : index (p * 5) ≤ lo := by lia
  have h5 : value (index (p * 5)) = p * 5 := value_index (by lia)
  have h7 : value (index (p * 7)) = p * 7 := value_index (by lia)
  rw [testBit_buildMaskK (by lia) hj hW] at h
  rcases h with ⟨hle, d, hd⟩ | ⟨hle, d, hd⟩
  · obtain ⟨c, hc⟩ := firstLocK_spec (A := index (p * 5)) (lo := lo) hm h5lo
    have hsum : lo + j = index (p * 5) + 2 * (p * (c + d)) := by lia
    have hval : value (lo + j) = p * 5 + 6 * (p * (c + d)) := by
      rw [hsum, value_add_two_mul, h5]
    exact ⟨5 + 6 * (c + d), by lia⟩
  · obtain ⟨c, hc⟩ := firstLocK_spec (A := index (p * 7)) (lo := lo) hm hlo
    have hsum : lo + j = index (p * 7) + 2 * (p * (c + d)) := by lia
    have hval : value (lo + j) = p * 7 + 6 * (p * (c + d)) := by
      rw [hsum, value_add_two_mul, h7]
    exact ⟨7 + 6 * (c + d), by lia⟩

/-- A run whose every step misses `j` leaves bit `j` as it found it. -/
public theorem testBit_segLoopK_of {s lo Wm1 seg start fuel j : Nat} (hseg : seg.testBit j = true)
    (hno : ∀ t, start ≤ t → t < start + fuel → testBitK s t = true →
      (buildMaskK (valueK t) Wm1 (firstLocK (indexK (valueK t * 5)) lo (valueK t * 2))
        (firstLocK (indexK (valueK t * 7)) lo (valueK t * 2)) 32).testBit j = false) :
    (segLoopK s lo Wm1 seg start fuel).testBit j = true := by
  induction fuel with
  | zero => exact hseg
  | succ n ih =>
    have ihn := ih fun t h1 h2 h3 => hno t h1 (by lia) h3
    rw [segLoopK_succ]
    cases hb : testBitK s (start + n) with
    | false => exact ihn
    | true =>
      rw [testBit_segMarkK, ihn, hno (start + n) (by lia) (by lia) hb]
      simp

/-- Every bit below `W` of the window a run starts from is set. -/
public theorem testBit_initSegK {W j : Nat} (hj : j < W) : (initSegK W).testBit j = true := by
  have hs1 : initSegK W = 2 ^ W - 1 := by
    unfold initSegK
    have hsl : Nat.shiftLeft 1 W = 1 <<< W := rfl
    have h : (1 : Nat) <<< W = 2 ^ W := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [hsl, h]
    rfl
  rw [hs1, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

/-- The bit of a number with no prime factor up to `B` survives the run. -/
@[expose] public def SegmentComplete (s B a W : Nat) : Prop :=
  ∀ j < W, (∀ q ≤ B, q.Prime → ¬ q ∣ value (index a + j)) →
    (segLoopK s (index a) (W - 1) (initSegK W) 1 (index B)).testBit j = true

set_option maxHeartbeats 1000000 in
-- As in `segmentSound_of`, the divisibility side conditions are closed against the whole context
-- and together pass the default limit.
/-- Every bit a completed run clears names a number with a prime factor up to `B`, stated as its
contrapositive. `B % 6` is 1 or 5 so that the run's last base index is `B` itself. -/
public theorem segmentComplete_of {s B a W : Nat} (hs : IsSieve B s)
    (hB6 : B % 6 = 1 ∨ B % 6 = 5) (hW : W - 1 < 2 ^ 32)
    (h7B : 7 * B ≤ a) : SegmentComplete s B a W := by
  intro j hj hno
  have hvB : value (index B) = B := value_index hB6
  refine testBit_segLoopK_of (testBit_initSegK hj) ?_
  · intro t h1 h2 hbit
    by_contra hmask
    rw [Bool.not_eq_false] at hmask
    rw [valueK_eq_value, indexK_eq_index] at hmask
    have ht0 : t ≠ 0 := Nat.one_le_iff_ne_zero.mp h1
    have ht5 : 5 ≤ value t := five_le_value ht0
    have h2' : t < index B + 1 := by rw [Nat.add_comm] at h2; exact h2
    have hmono := value_strictMono.monotone (Nat.lt_succ_iff.mp h2')
    have htB : value t ≤ B := by rw [hvB] at hmono; exact hmono
    rw [testBitK_eq_testBit] at hbit
    have hprime : (value t).Prime := (hs t ht0 htB).mp hbit
    have hmul : value t * 7 ≤ a :=
      calc value t * 7 = 7 * value t := Nat.mul_comm _ _
        _ ≤ 7 * B := Nat.mul_le_mul_left 7 htB
        _ ≤ a := h7B
    have hlo : index (value t * 7) ≤ index a := by
      unfold index
      exact Nat.div_le_div_right (Nat.sub_le_sub_right hmul 1)
    exact hno (value t) htB hprime
      (dvd_of_testBit_mask (value_mod6 t) ht5 hlo (Nat.le_sub_one_of_lt hj) hW hmask)

/-! ## Compiled twins

Executable copies of the definitions above, used by `run_segment` to compute the batch literals.
The kernel checks each batch equation, so a twin that disagreed would make `run_segment` fail. -/

meta def initSeg (W : Nat) : Nat := (1 <<< W) - 1

meta def firstLoc (A lo m : Nat) : Nat := (A + m * (lo / m + 1) - lo) % m

meta def segMark (seg p lo Wm1 : Nat) : Nat :=
  seg - (seg &&& buildMask p Wm1 (firstLoc (index (p * 5)) lo (p * 2))
    (firstLoc (index (p * 7)) lo (p * 2)) 32)

meta def segLoop (s lo Wm1 seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in [0:fuel] do
    let j := start + i
    if s &&& (1 <<< j) ≠ 0 then
      b := segMark b (value j) lo Wm1
  return b

/-- Twin of `seedK`. -/
meta def seedC (A M : Nat) : Nat := if A ≤ M then 1 <<< A else 0

/-- Twin of `buildMaskCK`. -/
meta def buildMaskC (p M A B n : Nat) : Nat := Id.run do
  let mut m := seedC A M ||| seedC B M
  for i in [0:n] do
    let sh := p <<< (i + 1)
    if sh ≤ M then
      m := m ||| (m <<< sh)
  return m

/-- Twin of `segMarkCK`. -/
meta def segMarkC (seg p lo Wm1 n : Nat) : Nat :=
  let A := firstLoc (index (p * 5)) lo (p * 2)
  let B := firstLoc (index (p * 7)) lo (p * 2)
  let mask := if p * 2 ≤ Wm1 then buildMaskC p Wm1 A B n else seedC A Wm1 ||| seedC B Wm1
  let hit := mask &&& seg
  if hit = 0 then seg else seg - hit

/-- Twin of `buildMaskNK`. -/
meta def buildMaskN (p M A B n : Nat) : Nat := Id.run do
  let terms := M / (p * 2) + 1
  let seeds := (1 <<< A) ||| (1 <<< B)
  let mut m := 0
  for i in [0:n] do
    let c := terms >>> (n - i)
    m := m ||| (m <<< (p * 2 * c))
    if (terms >>> (n - i - 1)) &&& 1 = 1 then
      m := m ||| (seeds <<< (p * 2 * (c * 2)))
  return m

/-- Twin of `buildMaskRK`. -/
meta def buildMaskR (p M A B : Nat) : Nat :=
  let m := p * 2
  ((2 ^ (m * (M / m + 1)) - 1) / (2 ^ m - 1)) * ((1 <<< A) ||| (1 <<< B))

/-- Twin of `segLoopStripeK`. -/
meta def segLoopStripe (s lo _Wm1 base acc start fuel : Nat) : Nat := Id.run do
  let mut a := acc
  let mut c := (s >>> start) &&& ((1 <<< fuel) - 1)
  for i in [0:fuel] do
    if c &&& 1 = 1 then
      let p := value (start + i)
      for X in [firstLoc (index (p * 5)) lo (p * 2), firstLoc (index (p * 7)) lo (p * 2)] do
        if base ≤ X && X - base ≤ 65535 then
          a := a ||| (1 <<< (X - base))
    c := c >>> 1
  return a

/-- Twin of `segMarkRK`. -/
meta def segMarkR (seg p lo Wm1 : Nat) : Nat :=
  let A := firstLoc (index (p * 5)) lo (p * 2)
  let B := firstLoc (index (p * 7)) lo (p * 2)
  let hit := buildMaskR p Wm1 A B &&& seg
  if hit = 0 then seg else seg - hit

/-- Twin of `segLoopSRK`. -/
meta def segLoopR (s lo Wm1 seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  let mut c := (s >>> start) &&& ((1 <<< fuel) - 1)
  for i in [0:fuel] do
    if c &&& 1 = 1 then
      b := segMarkR b (value (start + i)) lo Wm1
    c := c >>> 1
  return b

/-- Twin of `segMarkNK`. -/
meta def segMarkN (seg p lo Wm1 n : Nat) : Nat :=
  let A := firstLoc (index (p * 5)) lo (p * 2)
  let B := firstLoc (index (p * 7)) lo (p * 2)
  let hit := buildMaskN p Wm1 A B n &&& seg
  if hit = 0 then seg else seg - hit

/-- Twin of `segLoopSNK`, reading the base primes from the batch's own slice. -/
meta def segLoopN (s lo Wm1 n seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  let mut c := (s >>> start) &&& ((1 <<< fuel) - 1)
  for i in [0:fuel] do
    if c &&& 1 = 1 then
      b := segMarkN b (value (start + i)) lo Wm1 n
    c := c >>> 1
  return b

/-- Twin of `segAccLoopK`, joining the batch's masks into the running accumulator. -/
meta def segAccLoopC (s lo Wm1 n acc start fuel : Nat) : Nat := Id.run do
  let mut a := acc
  let mut c := (s >>> start) &&& ((1 <<< fuel) - 1)
  for i in [0:fuel] do
    if c &&& 1 = 1 then
      let p := value (start + i)
      let A := firstLoc (index (p * 5)) lo (p * 2)
      let B := firstLoc (index (p * 7)) lo (p * 2)
      a := a ||| buildMaskC p Wm1 A B n
    c := c >>> 1
  return a

/-- Twin of `segLoopCK`, reading the base primes from the batch's own slice of the base sieve.
Every batch literal in `runSegmentV` comes from here, and `segLoopK` and `segLoopCK` agree on all
of them: the seeds and rounds this drops carry bits above `Wm1` only, which `seg` never holds. -/
meta def segLoopC (s lo Wm1 n seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  let mut c := (s >>> start) &&& ((1 <<< fuel) - 1)
  for i in [0:fuel] do
    if c &&& 1 = 1 then
      b := segMarkC b (value (start + i)) lo Wm1 n
    c := c >>> 1
  return b

/-! ## The `run_segment` command -/

open Lean Elab Command Meta

/-- The statement `Nat.beq a b = true`. -/
meta def mkSegBeqTrue (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) a b) (mkConst ``Bool.true)

/-- The application `segLoopK s lo Wm1 seg start len`, with `start` and `len` as literals. -/
meta def mkSegLoopK (sE loE wE segE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``segLoopK) #[sE, loE, wE, segE, mkRawNatLit start, mkRawNatLit len]

/-- Batch length as a function of where the batch starts: short batches over the small primes,
whose masks are grown by doubling and are the widest the kernel holds at once, and long batches
over the large primes, whose masks are two bits. Each batch also leaves one window-sized literal
in the environment for the file's life, so the long end keeps that count down. -/
meta def batchLen (start : Nat) : Nat :=
  if start < 20000 then 256
  else if start < 300000 then 512
  else if start < 700000 then 768
  else 3072

/-- `batchLen` with a shorter run over the large primes. A batch holds about 869 KB per prime while
its theorem is checked, against one window-sized literal, 512 KB, per batch in the environment for
the file's life, so the two terms trade off and 3072 was measured against 8192 rather than
reasoned. -/
meta def batchLenWide (start : Nat) : Nat :=
  if start < 20000 then 256
  else if start < 300000 then 512
  else if start < 700000 then 768
  else 1536

/-- Add a theorem declaration with the given statement and proof term. -/
meta def addSegThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Sieve the window of `W` wheel positions starting at the number `a` by the base primes held in
the bitset `baseLit`, scanning `fuel` base indices in batches of `len`. Emits
`ns.segBits_{a}_{W}_{fuel}_{len} : Nat` and `ns.segEq_{a}_{W}_{fuel}_{len} : segLoopK … =
segBits_…`, the latter chained from one kernel-checked `Nat.beq` lemma per batch. `ns` is the
namespace the call sits in, so the same window can be built in two modules without a clash. -/
public meta def runSegment (ns baseLit : Name) (a W fuel len : Nat) : MetaM Unit := do
  if a % 6 ≠ 1 && a % 6 ≠ 5 then
    throwError "run_segment: the window start {a} is not 1 or 5 modulo 6"
  if W = 0 then throwError "run_segment: the window is empty"
  let env ← getEnv
  let some info := env.find? baseLit | throwError "run_segment: no base sieve {baseLit}"
  let some sVal := info.value?.bind Expr.rawNatLit?
    | throwError "run_segment: the base sieve {baseLit} is not a numeral"
  let lo := index a
  let wm1 := W - 1
  let step0 := Nat.max 1 len
  let sE := mkConst baseLit
  let loE := mkRawNatLit lo
  let wE := mkRawNatLit wm1
  let initE := mkApp (mkConst ``initSegK) (mkRawNatLit W)
  let lhsLoop := mkSegLoopK sE loE wE initE 1 fuel
  let tag := s!"{a}_{W}_{fuel}_{step0}"
  let parent := ns ++ Name.mkSimple s!"segEq_{tag}"
  let litName := ns ++ Name.mkSimple s!"segBits_{tag}"
  let mut bits := initSeg W
  let mut bitsE := initE
  let mut proof := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[Nat.mkType, lhsLoop]
  for i in [0:(fuel + step0 - 1) / step0] do
    let start := 1 + i * step0
    let owed := fuel - i * step0
    let stepN := Nat.min step0 owed
    let next := segLoop sVal lo wm1 bits start stepN
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
    addSegThm stepName
      (mkSegBeqTrue (mkSegLoopK sE loE wE bitsE start stepN) (mkRawNatLit next)) Lean.reflBoolTrue
    proof := if owed == stepN then
        mkAppN (mkConst ``segLoopK_last)
          #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
            proof, mkConst stepName]
      else
        mkAppN (mkConst ``segLoopK_chain)
          #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
            mkRawNatLit (owed - stepN), proof, mkConst stepName]
    bits := next
    bitsE := mkRawNatLit next
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := Nat.mkType,
      value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
  addSegThm parent (mkNatEq lhsLoop (mkConst litName)) proof
  let bVal := value fuel
  addSegThm (ns ++ Name.mkSimple s!"segEqI_{a}_{W}_{fuel}_{step0}")
    (mkNatEq (mkAppN (mkConst ``segRun)
        #[sE, mkRawNatLit a, mkRawNatLit W, mkRawNatLit bVal]) (mkConst litName))
    (mkAppN (mkConst ``segRun_of)
      #[sE, mkRawNatLit a, loE, mkRawNatLit W, wE, mkRawNatLit bVal, mkRawNatLit fuel,
        mkConst litName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
        mkConst parent])

/-- `run_segment a W fuel len` sieves the window of `W` wheel positions from `a` by the base
primes at wheel indices `1 … fuel`, in batches of `len` steps. A trailing numeral names another
base sieve by its bound, as `run_segment a W fuel len 100000000`; the default base is the
`1000000` sieve from `PrimeCert.SieveBase`. The emitted names carry all four numerals, so
distinct calls never collide. -/
elab "run_segment" aStx:num wStx:num fStx:num lStx:num bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    runSegment (← getCurrNamespace) base aStx.getNat wStx.getNat fStx.getNat lStx.getNat

/-- `runSegment` with a choice of loop and of batch assembly, for timing the draft variants
against each other. The loop is `mode % 4`: 0 is `segLoopK`, 1 is `segLoopCK`, 2 is `segLoopSK`
and 3 is `segLoopSCK`. Loops 2 and 3 emit one lemma checking the slice of the base sieve
(`…chunk_{i}`) per batch as well as the batch lemma (`…step_{i}`). Modes 0 to 3 assemble the
batches as one chain, modes 4 to 7 as a tree: each batch becomes a `…leaf_{i}` equation and each
`…join_{level}_{j}` combines two neighbours. Every mode ends at
`ns.segEqV_{tag} : segLoopK … = ns.segBitsV_{tag}`, the clamped loops through `segEq_of_clamped`.
Modes 0 to 7 compute the batch literals with the `segLoop` twin and modes 8 to 15 with the
`segLoopC` twin, the same eight assemblies otherwise, so the pair `m` and `m + 8` differs in the
command's own computation alone. Mode 16 joins each batch's masks into a running total and clears
the window once at the end, in place of clearing it per prime; it uses slices, the `segLoopC` twin
and a chain, so mode 11 is the arm to compare it against. -/
meta def runSegmentV (ns baseLit : Name) (mode a W fuel len : Nat) : MetaM Unit := do
  if a % 6 ≠ 1 && a % 6 ≠ 5 then
    throwError "run_segment_variant: the window start {a} is not 1 or 5 modulo 6"
  if W = 0 then throwError "run_segment_variant: the window is empty"
  if mode > 24 then throwError "run_segment_variant: mode {mode} is not 0 to 24"
  let env ← getEnv
  let some info := env.find? baseLit
    | throwError "run_segment_variant: no base sieve {baseLit}"
  let some sVal := info.value?.bind Expr.rawNatLit?
    | throwError "run_segment_variant: the base sieve {baseLit} is not a numeral"
  let sched := mode == 20 || mode == 21
  let wideTail := mode == 21
  let clamped := mode % 4 == 1 || mode % 4 == 3 || sched
  let slice := mode % 4 == 2 || mode % 4 == 3 || sched
  let tree := (mode % 8 ≥ 4 && !sched) || wideTail
  let fastTwin := mode ≥ 8
  let lo := index a
  let wm1 := W - 1
  let rounds := Nat.log2 wm1 + 1
  let step0 := Nat.max 1 len
  let sE := mkConst baseLit
  let loE := mkRawNatLit lo
  let wE := mkRawNatLit wm1
  let nE := mkRawNatLit rounds
  let initE := mkApp (mkConst ``initSegK) (mkRawNatLit W)
  let loopE (segE : Expr) (start n : Nat) : Expr :=
    if clamped then
      mkAppN (mkConst ``segLoopCK) #[sE, loE, wE, nE, segE, mkRawNatLit start, mkRawNatLit n]
    else mkSegLoopK sE loE wE segE start n
  let lhsLoop := loopE initE 1 fuel
  let tag := s!"{a}_{W}_{fuel}_{step0}_m{mode}"
  let parent := ns ++ Name.mkSimple s!"segEqV_{tag}"
  let litName := ns ++ Name.mkSimple s!"segBitsV_{tag}"
  if mode == 19 then
    -- Measurement only: the command's own computation, with one declaration emitted at the end,
    -- so its peak separates the loop's own footprint from the 2171 literals the other modes keep.
    let mut bitsL := initSeg W
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let owed := fuel - i * step0
      bitsL := segLoopC sVal lo wm1 rounds bitsL start (Nat.min step0 owed)
    addDecl <| Declaration.defnDecl
      { name := litName, levelParams := [], type := Nat.mkType,
        value := mkRawNatLit bitsL, hints := .regular 0, safety := .safe }
    return
  if mode == 24 then
    -- Measurement only: the same walk over the same primes, writing each prime's hits into one
    -- 65536-bit slice of the window instead of a number as wide as the window. Against mode 18 it
    -- gives what the width-dependent work costs per prime.
    let mut accT := 0
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let stepN := Nat.min step0 (fuel - i * step0)
      let next := segLoopStripe sVal lo wm1 0 accT start stepN
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let batchE := mkAppN (mkConst ``segLoopStripeK)
        #[mkRawNatLit cVal, loE, wE, mkRawNatLit 0, mkRawNatLit accT, mkRawNatLit start,
          mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
      accT := next
    return
  if mode == 23 then
    -- Measurement only: batches over an all-zero slice, so every step of the fold finds no prime
    -- and the window is returned unchanged. `fuel` steps in batches of `len` give the cost of the
    -- steps that a real run spends on positions holding no prime.
    let initLit := mkRawNatLit (initSeg W)
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let stepN := Nat.min step0 (fuel - i * step0)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let batchE := mkAppN (mkConst ``segLoopSCK)
        #[mkRawNatLit 0, loE, wE, nE, initLit, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE initLit) Lean.reflBoolTrue
    return
  if mode == 17 || mode == 18 || mode == 22 then
    -- Timing only: the per-batch checks with no chain and no final theorem, mode 17 through
    -- `segLoopSNK`, mode 18 through `segLoopSCK` and mode 22 through `segLoopSRK`, so the three
    -- isolate the mask builder.
    let mut bitsT := initSeg W
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let owed := fuel - i * step0
      let stepN := Nat.min step0 owed
      let next := if mode == 17 then segLoopN sVal lo wm1 rounds bitsT start stepN
        else if mode == 22 then segLoopR sVal lo wm1 bitsT start stepN
        else segLoopC sVal lo wm1 rounds bitsT start stepN
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let cE := mkRawNatLit cVal
      let chunkName := mkPrivateName env (parent ++ Name.mkSimple s!"chunk_{i}")
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let sliceE := mkApp2 (mkConst ``Nat.land)
        (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit start))
        (mkApp2 (mkConst ``Nat.sub)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit stepN)) (mkRawNatLit 1))
      addSegThm chunkName (mkSegBeqTrue sliceE cE) Lean.reflBoolTrue
      let batchE := if mode == 22 then
          mkAppN (mkConst ``segLoopSRK)
            #[cE, loE, wE, mkRawNatLit bitsT, mkRawNatLit start, mkRawNatLit stepN]
        else
          mkAppN (mkConst (if mode == 17 then ``segLoopSNK else ``segLoopSCK))
            #[cE, loE, wE, nE, mkRawNatLit bitsT, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
      bitsT := next
    return
  if mode == 16 then
    let mut acc := 0
    let mut accE := mkRawNatLit 0
    let mut covered := 0
    let mut proofA : Expr := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero])
      #[Nat.mkType, mkAppN (mkConst ``segAccLoopK)
        #[sE, loE, wE, nE, mkRawNatLit 0, mkRawNatLit 1, mkRawNatLit 0]]
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let owed := fuel - i * step0
      let stepN := Nat.min step0 owed
      let next := segAccLoopC sVal lo wm1 rounds acc start stepN
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let cE := mkRawNatLit cVal
      let chunkName := mkPrivateName env (parent ++ Name.mkSimple s!"chunk_{i}")
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let sliceE := mkApp2 (mkConst ``Nat.land)
        (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit start))
        (mkApp2 (mkConst ``Nat.sub)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit stepN)) (mkRawNatLit 1))
      addSegThm chunkName (mkSegBeqTrue sliceE cE) Lean.reflBoolTrue
      let batchE := mkAppN (mkConst ``segAccLoopSK)
        #[cE, loE, wE, nE, accE, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
      let leafName := mkPrivateName env (parent ++ Name.mkSimple s!"leaf_{i}")
      addSegThm leafName
        (mkNatEq (mkAppN (mkConst ``segAccLoopK)
          #[sE, loE, wE, nE, accE, mkRawNatLit start, mkRawNatLit stepN]) (mkRawNatLit next))
        (mkAppN (mkConst ``segAccLoopSK_leaf)
          #[sE, loE, wE, nE, accE, mkRawNatLit next, cE, mkRawNatLit start, mkRawNatLit stepN,
            mkConst chunkName, mkConst stepName])
      proofA := mkAppN (mkConst ``segAccLoopK_join)
        #[sE, loE, wE, nE, mkRawNatLit 0, accE, mkRawNatLit next, mkRawNatLit 1,
          mkRawNatLit covered, mkRawNatLit stepN, proofA, mkConst leafName]
      covered := covered + stepN
      acc := next
      accE := mkRawNatLit next
    let init := initSeg W
    let bits := init - (acc &&& init)
    addDecl <| Declaration.defnDecl
      { name := litName, levelParams := [], type := Nat.mkType,
        value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
    let accName := ns ++ Name.mkSimple s!"segAccV_{tag}"
    addSegThm accName
      (mkNatEq (mkAppN (mkConst ``segAccLoopK)
        #[sE, loE, wE, nE, mkRawNatLit 0, mkRawNatLit 1, mkRawNatLit fuel]) accE) proofA
    let clampedEq := mkAppN (mkConst ``segLoopCK_of_acc)
      #[sE, loE, wE, mkRawNatLit W, nE, accE, mkConst litName, mkRawNatLit fuel,
        mkConst accName, Lean.reflBoolTrue]
    addSegThm parent (mkNatEq (mkSegLoopK sE loE wE initE 1 fuel) (mkConst litName))
      (mkAppN (mkConst ``segEq_of_clamped)
        #[sE, loE, mkRawNatLit W, wE, nE, mkRawNatLit fuel, mkConst litName,
          Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, clampedEq])
    let bValA := value fuel
    addSegThm (ns ++ Name.mkSimple s!"segEqI_{tag}")
      (mkNatEq (mkAppN (mkConst ``segRun)
          #[sE, mkRawNatLit a, mkRawNatLit W, mkRawNatLit bValA]) (mkConst litName))
      (mkAppN (mkConst ``segRun_of)
        #[sE, mkRawNatLit a, loE, mkRawNatLit W, wE, mkRawNatLit bValA, mkRawNatLit fuel,
          mkConst litName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
          mkConst parent])
    return
  let mut bits := initSeg W
  let mut bitsE := initE
  let mut proof := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[Nat.mkType, lhsLoop]
  let mut nodes : Array (Name × Nat × Nat × Nat × Nat) := #[]
  let mut i := 0
  let mut start := 1
  while start ≤ fuel do
    let owed := fuel + 1 - start
    let stepN := Nat.min
      (if wideTail then batchLenWide start else if sched then batchLen start else step0) owed
    let next := if fastTwin then segLoopC sVal lo wm1 rounds bits start stepN
      else segLoop sVal lo wm1 bits start stepN
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
    let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
    let cE := mkRawNatLit cVal
    let chunkName := mkPrivateName env (parent ++ Name.mkSimple s!"chunk_{i}")
    if slice then
      let sliceE := mkApp2 (mkConst ``Nat.land)
        (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit start))
        (mkApp2 (mkConst ``Nat.sub)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit stepN)) (mkRawNatLit 1))
      addSegThm chunkName (mkSegBeqTrue sliceE cE) Lean.reflBoolTrue
      let batchE := if clamped then
          mkAppN (mkConst ``segLoopSCK)
            #[cE, loE, wE, nE, bitsE, mkRawNatLit start, mkRawNatLit stepN]
        else
          mkAppN (mkConst ``segLoopSK) #[cE, loE, wE, bitsE, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
    else
      addSegThm stepName (mkSegBeqTrue (loopE bitsE start stepN) (mkRawNatLit next))
        Lean.reflBoolTrue
    if tree then
      let leafName := mkPrivateName env (parent ++ Name.mkSimple s!"leaf_{i}")
      let leafProof := match clamped, slice with
        | false, false => mkAppN (mkConst ``segLoopK_of_beq)
            #[sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
              mkConst stepName]
        | true, false => mkAppN (mkConst ``segLoopCK_of_beq)
            #[sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
              mkConst stepName]
        | false, true => mkAppN (mkConst ``segLoopSK_leaf)
            #[sE, loE, wE, bitsE, mkRawNatLit next, cE, mkRawNatLit start, mkRawNatLit stepN,
              mkConst chunkName, mkConst stepName]
        | true, true => mkAppN (mkConst ``segLoopSCK_leaf)
            #[sE, loE, wE, nE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, mkConst chunkName, mkConst stepName]
      addSegThm leafName (mkNatEq (loopE bitsE start stepN) (mkRawNatLit next)) leafProof
      nodes := nodes.push (leafName, start, stepN, bits, next)
    else
      proof := match clamped, slice, owed == stepN with
        | false, false, true => mkAppN (mkConst ``segLoopK_last)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst stepName]
        | false, false, false => mkAppN (mkConst ``segLoopK_chain)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst stepName]
        | true, false, true => mkAppN (mkConst ``segLoopCK_last)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst stepName]
        | true, false, false => mkAppN (mkConst ``segLoopCK_chain)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst stepName]
        | false, true, true => mkAppN (mkConst ``segLoopSK_last)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst chunkName, mkConst stepName]
        | false, true, false => mkAppN (mkConst ``segLoopSK_chain)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst chunkName,
              mkConst stepName]
        | true, true, true => mkAppN (mkConst ``segLoopSCK_last)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst chunkName, mkConst stepName]
        | true, true, false => mkAppN (mkConst ``segLoopSCK_chain)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst chunkName,
              mkConst stepName]
    bits := next
    bitsE := mkRawNatLit next
    start := start + stepN
    i := i + 1
  if tree then
    let mut level := 0
    while nodes.size > 1 do
      let mut next : Array (Name × Nat × Nat × Nat × Nat) := #[]
      for j in [0:(nodes.size + 1) / 2] do
        if 2 * j + 1 < nodes.size then
          let (n1, s1, l1, b1, m1) := nodes[2 * j]!
          let (n2, _, l2, _, b2) := nodes[2 * j + 1]!
          let joinName := mkPrivateName env (parent ++ Name.mkSimple s!"join_{level}_{j}")
          let joinProof := if clamped then
              mkAppN (mkConst ``segLoopCK_join)
                #[sE, loE, wE, nE, mkRawNatLit b1, mkRawNatLit m1, mkRawNatLit b2,
                  mkRawNatLit s1, mkRawNatLit l1, mkRawNatLit l2, mkConst n1, mkConst n2]
            else
              mkAppN (mkConst ``segLoopK_join)
                #[sE, loE, wE, mkRawNatLit b1, mkRawNatLit m1, mkRawNatLit b2,
                  mkRawNatLit s1, mkRawNatLit l1, mkRawNatLit l2, mkConst n1, mkConst n2]
          addSegThm joinName
            (mkNatEq (loopE (mkRawNatLit b1) s1 (l1 + l2)) (mkRawNatLit b2)) joinProof
          next := next.push (joinName, s1, l1 + l2, b1, b2)
        else
          next := next.push nodes[2 * j]!
      nodes := next
      level := level + 1
    let some (topName, _, _, _, _) := nodes[0]?
      | throwError "run_segment_variant: the join tree is empty"
    proof := mkConst topName
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := Nat.mkType,
      value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
  let finalProof := if clamped then
      mkAppN (mkConst ``segEq_of_clamped)
        #[sE, loE, mkRawNatLit W, wE, nE, mkRawNatLit fuel, mkRawNatLit bits,
          Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, proof]
    else proof
  addSegThm parent (mkNatEq (mkSegLoopK sE loE wE initE 1 fuel) (mkConst litName)) finalProof
  let bVal := value fuel
  addSegThm (ns ++ Name.mkSimple s!"segEqI_{tag}")
    (mkNatEq (mkAppN (mkConst ``segRun)
        #[sE, mkRawNatLit a, mkRawNatLit W, mkRawNatLit bVal]) (mkConst litName))
    (mkAppN (mkConst ``segRun_of)
      #[sE, mkRawNatLit a, loE, mkRawNatLit W, wE, mkRawNatLit bVal, mkRawNatLit fuel,
        mkConst litName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
        mkConst parent])

/-- `run_segment_variant mode a W fuel len` is `run_segment a W fuel len` run through the loop and
the twin chosen by `mode`, 0 to 15 (see `runSegmentV`), with the same optional trailing base-sieve
bound. -/
elab "run_segment_variant" mStx:num aStx:num wStx:num fStx:num lStx:num bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    runSegmentV (← getCurrNamespace) base mStx.getNat aStx.getNat wStx.getNat fStx.getNat
      lStx.getNat

/-! ## Worked instances

A ladder of windows well above the base range, built smallest first. The arguments are
`a W fuel len`: the window of `W` wheel positions from `a`, sieved by the base primes at wheel
indices `1 … fuel` (the numbers up to `value fuel`), in `len`-step batches.

The last line is the widest that has been through the kernel here: 1024 wheel positions from
`10^16 + 1`, sieved by every prime up to `10^6`. Wider or deeper cases belong in
`PrimeCertTest/SegBench`, which is not part of `defaultTargets`. -/

run_segment 1000000000001 16 100 16
run_segment 1000000000001 64 100 16
run_segment 100000000000001 16 100 16
run_segment 10000000000000001 16 100 16
run_segment 10000000000000001 256 1000 16
run_segment 10000000000000001 1024 3333 16
run_segment 10000000000000001 4096 3333 16
run_segment 10000000000000001 1024 33333 16
run_segment 10000000000000001 256 333333 512
run_segment 1000000000000000001 64 100 16
run_segment_variant 16 1000000000001 64 100 16
run_segment 10000000000000001 1024 333333 512

end PrimeCert.Sieve
