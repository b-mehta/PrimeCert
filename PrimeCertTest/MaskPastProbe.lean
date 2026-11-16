/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Sieve

/-! # A divisor whose first locations are past the window

The skipped side of the certificate asks every skipped divisor to divide one product `P`, so it
carries one factor per skipped divisor. Counting says most skipped divisors are skipped for a
reason that has nothing to do with the window's live positions: they have no multiple at a window
position at all. That is 84.95% of the skipped set at `10^16` and 97.55% at `10^18`.

This asks whether such a divisor has a second route to the same conclusion, one that mentions no
product. It does. `firstLocK` returns an offset below `2 * p`, so a divisor with no position in
the window is exactly one whose two first locations both exceed `Wm1`, and every bit
`buildMaskK` sets lies at or above the lower of them. The mask is not zero, which is the thing
worth getting right: it carries bits at `A` and `B` and their doublings, all of them past the
window, so it meets the window in nothing.

What that would be worth is a measurement and not a thing counts can say. This file only settles
that the statement is true and provable. -/

namespace PrimeCert.Sieve.MaskPastProbe

/-- Every bit `buildMaskK` sets lies at or above both of its two seeds, so a bit below both is
clear however many doubling rounds are taken. -/
theorem testBit_buildMaskK_of_lt {p M A B : Nat} :
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

/-- And so the mask meets the window in nothing, which is all `segMarkK` needs to leave the window
alone. The window's bits stop at `Wm1` and the mask's start above it, so no position is shared.

This is the hypothesis `segMarkK_eq_self_of_not_dvd` reaches through the product and the gcd. A
divisor with no position in the window reaches it without naming a product at all.

The window's own bound is taken as the bits it has rather than as `seg < 2 ^ (Wm1 + 1)`, which is
the form `segMarkK_eq_self_of_not_dvd` already turns that bound into: this file imports no mathlib,
and the step from the bound to the bits is the one line there that needs it. -/
theorem land_buildMaskK_eq_zero {seg p M A B n Wm1 : Nat}
    (hseg : ∀ j, Wm1 < j → Nat.testBit seg j = false)
    (hA : Wm1 < A) (hB : Wm1 < B) : Nat.land seg (buildMaskK p M A B n) = 0 := by
  have hland : Nat.land seg (buildMaskK p M A B n) = seg &&& buildMaskK p M A B n := rfl
  rw [hland]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hj : j ≤ Wm1
  · rw [testBit_buildMaskK_of_lt n j (by omega) (by omega), Bool.and_false]
  · rw [hseg j (by omega), Bool.false_and]

end PrimeCert.Sieve.MaskPastProbe
