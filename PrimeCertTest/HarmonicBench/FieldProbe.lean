/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.QuickRfl

/-! # What one prefix sum over a field-wide segment costs the kernel

A design for the leaves of the Bach, Klyve and Sorenson expansion gives each of the 262144
positions of a segment a 64 bit field rather than one bit, so the whole segment is a natural
number of 16777216 bits. Answering one leaf is then a bitwise and against the low `64 * (y + 1)`
bits, followed by a remainder modulo `2 ^ 64 - 1`, which sums the fields because `2 ^ 64` is
congruent to `1` there.

`andHalf` and `modHalf` price those two steps at a leaf halfway along the segment, `modFull` at
the far end, and `clearOne` prices one step of the sieve on the same width for comparison. The
operand is all ones rather than a real segment, so these are sizes rather than contents.
-/

namespace PrimeCert.FieldProbe

/-- All ones, `64 * 262144` bits wide: one field per position of a segment. -/
@[expose] public def wideK : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 16777216)) (nat_lit 1)

/-- All ones in the low `64 * 131073` bits: the mask a leaf halfway along the segment uses. -/
@[expose] public def halfMaskK : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 8388672)) (nat_lit 1)

/-- The modulus that turns a field sum into a remainder. -/
@[expose] public def fieldOnesK : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 64)) (nat_lit 1)

set_option maxRecDepth 4000000 in
theorem andHalf : Nat.beq (Nat.land wideK halfMaskK) halfMaskK = true := by quickRfl

set_option maxRecDepth 4000000 in
theorem modHalf :
    Nat.beq (Nat.mod (Nat.land wideK halfMaskK) fieldOnesK) (nat_lit 0) = true := by quickRfl

set_option maxRecDepth 4000000 in
theorem modFull : Nat.beq (Nat.mod wideK fieldOnesK) (nat_lit 0) = true := by quickRfl

set_option maxRecDepth 4000000 in
theorem clearOne :
    Nat.beq (Nat.sub wideK (Nat.land wideK halfMaskK))
      (Nat.sub wideK halfMaskK) = true := by quickRfl

end PrimeCert.FieldProbe
