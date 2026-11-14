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

/-! ## The step the certificate rests on

Everything above is arithmetic the kernel can check. This is the part that makes checking it mean
something: a gcd of 1 rules out a shared divisor. Written here because it needs nothing but core,
which was worth finding out before assuming the soundness work needs the main module too. -/

/-- If two numbers are coprime, nothing above 1 divides both. -/
public theorem eq_one_of_dvd_gcd_one {a b p : Nat}
    (h : Nat.gcd a b = 1) (hpa : p ∣ a) (hpb : p ∣ b) : p = 1 := by
  have hp : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
  rw [h] at hp
  exact Nat.dvd_one.mp hp

/-- The form the certificate uses it in: a skipped divisor cannot divide a live value, given the
chunk's product is coprime to the product of the skipped divisors. `hv` is that the live value
divides its chunk's product, which the tree gives, and `hd` that the divisor divides theirs. -/
public theorem not_dvd_of_coprime_products {live skip v d : Nat}
    (h : Nat.gcd live skip = 1) (hv : v ∣ live) (hd : d ∣ skip) (hd1 : d ≠ 1) : ¬ (d ∣ v) := by
  intro hdv
  exact hd1 (eq_one_of_dvd_gcd_one h (Nat.dvd_trans hdv hv) hd)

/-! ## At the size the design actually calls for

The checks above use four-record chunks, which say the definitions are right and nothing about
whether they reduce at the chunk the sizing settled on. These are 64 records in 256 slots at depth
8, so they exercise the design's depth and the cutoff over most of the slots at once. The literals
are generated by `scripts/gen_chunk_probe.py` rather than typed.

256 records would be the honest size, but packed they are a 1230-digit literal, which is more than
a source file should carry; the depth is the same either way. -/

private def recsChunk : Nat := 172815503265868610333461859967230987341955653381567929661261965768265244975406494921669806199637631956627798690107337269033879389350441917480266470061013647898759588360046448225673629563498234155683648075918231703427794403217332430084192780864968972684231726872307962776499854565510227023066276530613190656

example : prodChunkK recsChunk 0 64 8 0 =
    21717446281257584122923225135103647078455328610484106362678751700744779800850179864731058957904517103498056793212890625 := rfl

example : asmChunkK recsChunk 64 8 0 = 18446744073709551615 := rfl

end PrimeCert.SegTune.ChunkProductProbe
