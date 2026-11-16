/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Sieve

/-! # The divisors with no position in the window

The skipped side of the certificate puts every skipped divisor into one product. Counting says
most of them are skipped for a reason that never touches the window's live positions: they have no
multiple at a window position at all. That is 4688449 of the 5519007 skipped at `10^16`, and
49281838 of 50519424 at `10^18`.

Such a divisor needs no product. `firstLocK` returns an offset below `2 * p`, so having no
position in the window is exactly having both first locations above `Wm1`, and a mask seeded past
the window meets the window in nothing.

The point of this file is the shape of the check rather than the check itself. Stated one divisor
at a time it is one kernel statement per divisor, millions of them, which is the element-serial
pattern the metaprogramming notes rule out twice. Stated as a fold over a batch it is one
statement per batch, the same shape the run already emits for marking, and the per-divisor work
inside it is a modular reduction and two comparisons on numbers the size of `p`.

What it must not be is a loop that builds masks. `segLoopK` reaches `segMarkK` and then
`buildMaskK`, which seeds with `Nat.shiftLeft 1 A`; for a divisor with no position `A` is above
`Wm1` by definition and below `2 * p`, so that seed is a number of up to some hundred million bits
at a `10^8` bound. Running the loop over these divisors would build one such mask apiece, which is
the per-divisor work the skipped side exists to avoid. Nothing below mentions `segLoopK`,
`segMarkK` or `buildMaskK`, and a later version that reaches for one of them has lost the point.

Whether this costs less than carrying the same divisors in the product is a measurement, not a
thing the shape decides.

`firstLocK` itself lives in `SegmentedSieve`, which imports this file rather than the other way
round, so its body is written out here. That also keeps a wrapper unfold off the kernel's path,
which is what the notes ask for in a reduced position anyway. -/

namespace PrimeCert.Sieve

/-- The first offset at or after `lo` in the progression `A, A + m, A + 2m, …`, as a local offset
below `m`. This is `SegmentedSieve.firstLocK`, written in primitive operations. -/
@[expose] public def firstOffK (A lo m : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add A m) (Nat.mod lo m)) m

/-- Whether the divisor `p` has no multiple at any position of the window: both of the two
progressions it would mark start past `Wm1`.

The two progressions are the coprime-to-6 multiples `5p, 11p, 17p, …` and `7p, 13p, 19p, …`, which
in index space are arithmetic progressions of step `2p`. -/
@[expose] public def noPosAtK (lo Wm1 p : Nat) : Bool :=
  Bool.and
    (Nat.blt Wm1 (firstOffK (indexK (Nat.mul p 5)) lo (Nat.mul p 2)))
    (Nat.blt Wm1 (firstOffK (indexK (Nat.mul p 7)) lo (Nat.mul p 2)))

/-- Every divisor named by the low `fuel` bits of `c` has no position in the window.

`c` holds one bit per index, bit `i` standing for the divisor at index `start + i`. The bit is
tested by shifting the probe up rather than the bitset down, so the shift moves the constant `1`
and not `c`. -/
@[expose] public noncomputable def noPosFoldK (c lo Wm1 start fuel : Nat) : Bool :=
  Nat.rec true
    (fun i acc =>
      (Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 i))).rec acc
        (Bool.and acc (noPosAtK lo Wm1 (valueK (Nat.add start i)))))
    fuel

/-- The step the emitter's statement is read against, in the exact `Bool.rec` form the definition
uses, so that a proof about a batch can peel its top index without unfolding `Nat.rec` by hand. -/
public theorem noPosFoldK_succ {c lo Wm1 start fuel : Nat} :
    noPosFoldK c lo Wm1 start (fuel + 1)
      = Bool.rec (noPosFoldK c lo Wm1 start fuel)
          (Bool.and (noPosFoldK c lo Wm1 start fuel)
            (noPosAtK lo Wm1 (valueK (Nat.add start fuel))))
          (Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 fuel))) := rfl

/-! ## The mask of a divisor with no position

`buildMaskK` is seeded with bits at `A` and `B` unconditionally, so the mask of such a divisor is
not zero. What is true is that every bit it sets lies at or above the lower of the two seeds, so
the mask sits entirely past the window and meets it in nothing. That is all `segMarkK` needs. -/

/-- Every bit `buildMaskK` sets lies at or above both of its two seeds, so a bit below both is
clear however many doubling rounds are taken. -/
public theorem testBit_buildMaskK_of_lt {p M A B : Nat} :
    ∀ n j, j < A → j < B → Nat.testBit (buildMaskK p M A B n) j = false := by
  intro n
  induction n with
  | zero =>
    intro j hA hB
    have h : buildMaskK p M A B 0 = (Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B) := rfl
    rw [h]
    have hor : (Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B) = (1 <<< A) ||| (1 <<< B) := rfl
    rw [hor, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
    grind
  | succ n ih =>
    intro j hA hB
    have h : buildMaskK p M A B (n + 1) =
        ((Nat.shiftLeft p (n + 1)).ble M).rec (buildMaskK p M A B n)
          ((buildMaskK p M A B n).lor
            ((buildMaskK p M A B n).shiftLeft (Nat.shiftLeft p (n + 1)))) := rfl
    rw [h]
    cases hb : (Nat.shiftLeft p (n + 1)).ble M with
    | false => exact ih j hA hB
    | true =>
      have hor : (buildMaskK p M A B n).lor
            ((buildMaskK p M A B n).shiftLeft (Nat.shiftLeft p (n + 1))) =
          (buildMaskK p M A B n) ||| ((buildMaskK p M A B n) <<< (Nat.shiftLeft p (n + 1))) := rfl
      rw [hor, Nat.testBit_or, Nat.testBit_shiftLeft, ih j hA hB]
      have hsub : ∀ s, j - s < A ∧ j - s < B := fun s => ⟨by omega, by omega⟩
      have := ih (j - Nat.shiftLeft p (n + 1)) (hsub _).1 (hsub _).2
      grind

/-- And so the mask meets the window in nothing. The window's bits stop at `Wm1` and the mask's
start above it, so no position is shared.

The window's bound is taken as the bits it has rather than as `seg < 2 ^ (Wm1 + 1)`, which is the
form `segMarkK_eq_self_of_not_dvd` already turns that bound into; this module imports no mathlib,
and that one step is the part which needs it. -/
public theorem land_buildMaskK_eq_zero {seg p M A B n Wm1 : Nat}
    (hseg : ∀ j, Wm1 < j → Nat.testBit seg j = false)
    (hA : Wm1 < A) (hB : Wm1 < B) : Nat.land seg (buildMaskK p M A B n) = 0 := by
  have hland : Nat.land seg (buildMaskK p M A B n) = seg &&& buildMaskK p M A B n := rfl
  rw [hland]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hj : j ≤ Wm1
  · rw [testBit_buildMaskK_of_lt n j (by omega) (by omega), Bool.and_false]
  · rw [hseg j (by omega), Bool.false_and]

/-! ## Reading the fold back

The emitter states one fold per batch. What a proof needs from it is the fact about a single
divisor, so this takes the statement apart again: a batch whose fold is `true` gives, for every
bit it names, that that divisor has no position in the window.

Together with `land_buildMaskK_eq_zero` above, that is everything the skipped side needs for
these divisors, and none of it mentions a product. -/

/-- Every divisor a true fold names has no position in the window. -/
public theorem noPosAtK_of_noPosFoldK {c lo Wm1 start : Nat} : ∀ fuel i,
    noPosFoldK c lo Wm1 start fuel = true → i < fuel →
    Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 i)) = true →
    noPosAtK lo Wm1 (valueK (Nat.add start i)) = true := by
  intro fuel
  induction fuel with
  | zero => intro i _ hi _; omega
  | succ n ih =>
    intro i hfold hi hbit
    rw [noPosFoldK_succ] at hfold
    have hsplit : i < n ∨ i = n := by omega
    cases hb : Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 n)) with
    | false =>
      simp only [hb] at hfold
      rcases hsplit with h | h
      · exact ih i hfold h hbit
      · rw [h] at hbit
        rw [hbit] at hb
        exact absurd hb (by simp)
    | true =>
      simp only [hb, Bool.and_eq_true] at hfold
      rcases hsplit with h | h
      · exact ih i hfold.1 h hbit
      · rw [h]
        exact hfold.2

/-- **The no-position argument, end to end up to `SegmentedSieve`.** A batch whose fold is `true`
names only divisors whose masks miss the window entirely.

`SegmentedSieve.firstLocK` has the same body as `firstOffK` and `segMarkK` takes `32` doubling
rounds, so applying this at a marking step is a matter of matching those two up. No product, no
gcd, and nothing here mentions `segLoopK`, `segMarkK` or a mask build. -/
public theorem land_mask_eq_zero_of_noPosFoldK {c lo Wm1 start fuel i seg n : Nat}
    (hfold : noPosFoldK c lo Wm1 start fuel = true) (hi : i < fuel)
    (hbit : Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 i)) = true)
    (hseg : ∀ j, Wm1 < j → Nat.testBit seg j = false) :
    Nat.land seg (buildMaskK (valueK (Nat.add start i)) Wm1
        (firstOffK (indexK (Nat.mul (valueK (Nat.add start i)) 5)) lo
          (Nat.mul (valueK (Nat.add start i)) 2))
        (firstOffK (indexK (Nat.mul (valueK (Nat.add start i)) 7)) lo
          (Nat.mul (valueK (Nat.add start i)) 2)) n) = 0 := by
  have hat := noPosAtK_of_noPosFoldK fuel i hfold hi hbit
  rw [noPosAtK, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at hat
  exact land_buildMaskK_eq_zero hseg hat.1 hat.2

/-! ## The compiled twin

`Bool.rec` is what the kernel wants and the code generator does not compile it, so `noPosFoldK`
cannot be run. This is the mirror the emitter computes with, in the usual arrangement: the
emitter splices the twin's answer into the statement and `reflBoolTrue` rejects it if the two
disagree, so the twin needs no correctness proof of its own. It gets one anyway, below, because
it is cheap here and it means a test of either is a test of both.

`noPosAtK` needs no twin: it is `Bool.and` of two `Nat.blt`s, with no recursor in it, so it
compiles and `PrimeCertTest.NoPosProbe` tests it directly. -/

/-- `noPosFoldK` in the ordinary API, reading the bits the same way. -/
public def noPosFold (c lo Wm1 start : Nat) : Nat → Bool
  | 0 => true
  | i + 1 =>
    cond (Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 i)))
      (Bool.and (noPosFold c lo Wm1 start i) (noPosAtK lo Wm1 (valueK (Nat.add start i))))
      (noPosFold c lo Wm1 start i)

/-- The kernel form and the twin agree, so a test of one is a test of both. -/
public theorem noPosFoldK_eq (c lo Wm1 start : Nat) : ∀ fuel,
    noPosFoldK c lo Wm1 start fuel = noPosFold c lo Wm1 start fuel := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ n ih =>
    rw [noPosFoldK_succ, ih]
    cases h : Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 n)) <;> simp only [noPosFold, h, cond]

end PrimeCert.Sieve
