/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-! # The certificate's per-chunk product, standalone

The record-driven certificate needs a kernel definition multiplying the values named by a chunk of
records. That belongs in `PrimeCert/SegmentedSieve.lean` eventually, but this box cannot compile
that file, so it is written here against a local copy of `valueK` and imports nothing. The two are
related by `rfl` when this moves across, since the copy below is the same arithmetic.

**The tests are `rfl`, not `#guard`.** The definition is `noncomputable`, built from `Nat.rec` the
way the file's other kernel definitions are, so there is nothing for `#guard` to evaluate. `rfl`
makes the kernel reduce it, which is the mechanism the certificate actually relies on, so these
check the thing that matters rather than a compiled shadow of it.

Throwaway, and the reason it exists is that two certificate shapes already died: one inspecting the
window a bit at a time, one the same thing as a tree. This shape reads only a small packed record
set per statement. -/

namespace PrimeCert.SegTune.ChunkProductProbe

/-- Local copy of `valueK`: the `k`-th positive integer coprime to 6, as `(3k+1) + k % 2`, giving
1, 5, 7, 11, 13, 17, … -/
@[expose] public noncomputable def valK (k : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul k 3) 1) (Nat.mod k 2)

/-- The product of the values named by one chunk of sixteen-bit records.

`recs` packs the chunk's positions, `cnt` of them, and slots at or past `cnt` contribute 1 so the
chunk may be rounded up to a power of two. `d` is the log of the slot count and `off` the first
slot, so the recursion has depth `d` over `2 ^ d` leaves rather than a chain of `2 ^ d`.

The point of the shape is that `recs` is **one chunk**, a few hundred records, not a whole slice:
a leaf reaches its field by shifting `recs`, so the cost of that shift is the size of a chunk and
not the size of the window. A version taking a slice's 170 KB of records would repeat the trap
that killed the two previous shapes. -/
@[expose] public noncomputable def prodChunkK (recs lo cnt d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o => (Nat.blt o cnt).rec 1
      (valK (Nat.add lo (Nat.land (Nat.shiftRight recs (Nat.mul o 16)) 65535))))
    (fun k ih o => Nat.mul (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

/-- The bits named by one chunk of records, assembled.

The other half of the certificate's kernel vocabulary. A product over records is only worth
anything alongside a statement that the records are the right ones, and the way the route already
does that is to assemble them and compare with a literal the emitter supplies. Assembling needs
shifts and `lor` alone, so it needs nothing the product did not.

Same shape and same reason as `prodChunkK`: one chunk at a time, slots past `cnt` contributing
nothing, depth `d` over `2 ^ d` leaves. A slice is then the `lor` of its chunks, and the emitter
knows what that should equal. -/
@[expose] public noncomputable def asmChunkK (recs cnt d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o => (Nat.blt o cnt).rec 0
      (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight recs (Nat.mul o 16)) 65535)))
    (fun k ih o => Nat.lor (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

/-! ## Checks, by kernel reduction -/

-- valK gives the integers coprime to 6.
example : valK 0 = 1 := rfl
example : valK 1 = 5 := rfl
example : valK 2 = 7 := rfl
example : valK 3 = 11 := rfl
example : valK 4 = 13 := rfl

-- Three records naming positions 0, 1 and 2, in four slots: 1 * 5 * 7, with the fourth slot 1.
example : prodChunkK (0 ||| (1 <<< 16) ||| (2 <<< 32)) 0 3 2 0 = 35 := rfl

-- The same three records with the slot count honoured: cnt 2 stops after 1 * 5.
example : prodChunkK (0 ||| (1 <<< 16) ||| (2 <<< 32)) 0 2 2 0 = 5 := rfl

-- An empty chunk is the empty product.
example : prodChunkK 0 0 0 2 0 = 1 := rfl

-- `lo` shifts which values the positions name: positions 0 and 1 at lo = 3 are valK 3 and valK 4.
example : prodChunkK (0 ||| (1 <<< 16)) 3 2 1 0 = 143 := rfl

-- Eight slots, four records at positions 0, 2, 4, 6: 1 * 7 * 13 * valK 6, and valK 6 = 19.
example : valK 6 = 19 := rfl
example : prodChunkK (0 ||| (2 <<< 16) ||| (4 <<< 32) ||| (6 <<< 48)) 0 4 3 0 = 1729 := rfl

-- Records naming positions 0, 1 and 2 assemble to bits 0, 1 and 2.
example : asmChunkK (0 ||| (1 <<< 16) ||| (2 <<< 32)) 3 2 0 = 7 := rfl

-- The cutoff applies here too: two of the three records give bits 0 and 1.
example : asmChunkK (0 ||| (1 <<< 16) ||| (2 <<< 32)) 2 2 0 = 3 := rfl

-- An empty chunk assembles to nothing, which is the identity for `lor` as 1 is for `mul`.
example : asmChunkK 0 0 2 0 = 0 := rfl

-- Scattered positions. Kept small deliberately: a position near the top of a slice would have the
-- kernel build a 65536-bit number to compare against, which trips the recursion limit and tests
-- the test rather than the definition.
example : asmChunkK (5 ||| (9 <<< 16)) 2 1 0 = 544 := rfl
example : asmChunkK 20 1 0 0 = 1048576 := rfl

-- The two halves agree about which records they are reading: the same chunk assembles to three
-- bits and multiplies to the product of the three values those bits stand for.
example : asmChunkK (0 ||| (1 <<< 16) ||| (2 <<< 32)) 3 2 0 = 7 := rfl
example : prodChunkK (0 ||| (1 <<< 16) ||| (2 <<< 32)) 0 3 2 0 = 35 := rfl

end PrimeCert.SegTune.ChunkProductProbe
