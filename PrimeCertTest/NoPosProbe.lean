/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.NoPos
public meta import PrimeCert.NoPos

/-! # Does the fold say what it is meant to say?

The reference below decides the same question the slow and obvious way: walk every position of
the window and see whether the divisor divides the value there. It shares nothing with the
definition under test beyond `valueK`, so a disagreement is a real one rather than the same
mistake written twice.

The numbers are small on purpose. These check that the condition on the two first locations is
the condition on the window, which is a statement about the arithmetic and not about the depth. -/

namespace PrimeCert.Sieve.NoPosProbe

/-- Does `p` divide the value at some position of the window? Walks the positions one by one. -/
def hitsWindow (lo Wm1 p : Nat) : Bool := Id.run do
  let mut j := 0
  while j ≤ Wm1 do
    if valueK (lo + j) % p == 0 then
      return true
    j := j + 1
  return false

/-- The fold's answer, by the obvious walk over the bits and the positions. -/
def hitsFold (c lo Wm1 start fuel : Nat) : Bool := Id.run do
  let mut acc := true
  for i in [0:fuel] do
    if (c >>> i) % 2 == 1 then
      acc := acc && !hitsWindow lo Wm1 (valueK (start + i))
  return acc

-- One divisor at a time, over a range of indices so both the hitting and the missing cases occur.
#guard (List.range 200).all fun k =>
  noPosAtK 500 63 (valueK (120 + k)) == !hitsWindow 500 63 (valueK (120 + k))

-- Again with the window elsewhere: `firstOffK` is the only part that reads `lo`, so one `lo`
-- would leave it untested.
#guard (List.range 200).all fun k =>
  noPosAtK 4097 255 (valueK (300 + k)) == !hitsWindow 4097 255 (valueK (300 + k))

-- Divisors small enough to strike many times, where having a position is the common case.
#guard (List.range 60).all fun k =>
  noPosAtK 77 511 (valueK (2 + k)) == !hitsWindow 77 511 (valueK (2 + k))

-- The fold over a batch agrees with the walk, over batches whose bits are a mixture.
#guard (List.range 40).all fun k =>
  noPosFold (0xA5F03C69 >>> (k % 8)) 500 63 (120 + k) 32
    == hitsFold (0xA5F03C69 >>> (k % 8)) 500 63 (120 + k) 32

-- A batch with no bits set says `true`: an empty batch is no obstacle, which is the case that
-- broke the sorted-batch emitter at 10^16.
#guard noPosFold 0 500 63 120 32 == true

-- And the check is not vacuously true: some single-divisor batch in this range says `false`.
#guard (List.range 200).any fun k => noPosFold 1 77 511 (2 + k) 1 == false

/-! ## At the size the run uses

The checks above use windows of 64 to 512 positions, which exercise the arithmetic but leave open
whether anything turns over at the real size. A window is `W = 4194304` positions, so `Wm1` is
4194303, and a window start near `10^14` is index 33333333333333.

Two groups of divisors, because where they sit decides which answer they give. The window spans
12582912 integers, so a divisor at the start of the widest band near 2097152 has about six
multiples inside it and in practice always has a position. The divisors with no position sit near
the bound, which is `10^7` at this depth, where a divisor has one or two multiples in that span
and often none at a position. Each divisor walks all 4194304 positions in the reference. -/

#guard (List.range 8).all fun k =>
  noPosAtK 33333333333333 4194303 (valueK (699050 + k))
    == !hitsWindow 33333333333333 4194303 (valueK (699050 + k))

#guard (List.range 8).all fun k =>
  noPosAtK 33333333333333 4194303 (valueK (3333333 + k))
    == !hitsWindow 33333333333333 4194303 (valueK (3333333 + k))

-- Both answers occur at this size, so the agreement above is not one answer repeated.
#guard (List.range 8).any fun k => noPosAtK 33333333333333 4194303 (valueK (699050 + k)) == false

#guard (List.range 8).any fun k => noPosAtK 33333333333333 4194303 (valueK (3333333 + k)) == true

end PrimeCert.Sieve.NoPosProbe
