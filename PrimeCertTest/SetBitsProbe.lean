/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import SieveEmit.Core

/-! # `setBitsLow` against a reference

The halving version has to agree with a bit-at-a-time scan, in content and in order, or the record
packing quietly shifts and every chunk statement after it is about the wrong positions. The
reference below is the slow, obviously-correct reading, and the checks compare the two on the
shapes that matter: empty, dense, sparse, a single bit at each boundary a split can fall on, and
widths that are not multiples of 64.

Throwaway, and it builds in about two seconds, which is why it is a file and not a guess. -/

namespace PrimeCert.SegTune.SetBitsProbe

open SieveEmit

/-- The slow reading: test every position in turn. -/
def refBits (c len : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [0:len] do
    if c.testBit i then
      out := out.push i
  return out

/-- A spread of positions to set, chosen to land either side of the word and split boundaries. -/
def sample : List Nat :=
  [0, 1, 63, 64, 65, 127, 128, 129, 191, 255, 256, 257, 383, 511, 512, 513, 1000, 1023, 1024,
    1025, 2047, 2048, 4095, 4096, 8191]

def ofPositions (ps : List Nat) : Nat := ps.foldl (fun a p => a ||| (1 <<< p)) 0

#guard setBitsLow 0 0 == refBits 0 0
#guard setBitsLow 0 8192 == refBits 0 8192
#guard setBitsLow 1 1 == refBits 1 1
#guard setBitsLow 255 8 == refBits 255 8

-- Dense: every bit of a word, and of a span crossing several split boundaries.
#guard setBitsLow ((1 <<< 64) - 1) 64 == refBits ((1 <<< 64) - 1) 64
#guard setBitsLow ((1 <<< 300) - 1) 300 == refBits ((1 <<< 300) - 1) 300
#guard setBitsLow ((1 <<< 8192) - 1) 8192 == refBits ((1 <<< 8192) - 1) 8192

-- The spread, read at several widths, including widths that cut it short.
#guard setBitsLow (ofPositions sample) 8192 == refBits (ofPositions sample) 8192
#guard setBitsLow (ofPositions sample) 1000 == refBits (ofPositions sample) 1000
#guard setBitsLow (ofPositions sample) 257 == refBits (ofPositions sample) 257
#guard setBitsLow (ofPositions sample) 65 == refBits (ofPositions sample) 65

-- Widths that are not multiples of 64, where the split has to round and still cover the top.
#guard setBitsLow (ofPositions sample) 100 == refBits (ofPositions sample) 100
#guard setBitsLow (ofPositions sample) 129 == refBits (ofPositions sample) 129
#guard setBitsLow (ofPositions sample) 4097 == refBits (ofPositions sample) 4097

-- Bits above `len` are not reported, which is what keeps a batch a batch.
#guard setBitsLow (1 <<< 200) 100 == #[]
#guard setBitsLow ((1 <<< 200) ||| 7) 100 == #[0, 1, 2]

-- A single bit at each boundary a split can land on, read at a width well past it.
#guard setBitsLow (1 <<< 64) 8192 == #[64]
#guard setBitsLow (1 <<< 4096) 8192 == #[4096]
#guard setBitsLow (1 <<< 8191) 8192 == #[8191]

-- Sparse and high, the shape the upper reaches of a divisor mask take.
#guard setBitsLow ((1 <<< 7000) ||| (1 <<< 7001) ||| (1 <<< 8000)) 8192
  == #[7000, 7001, 8000]

/-! ## `liveRecords` against the packing it replaces

The pairwise packing has to produce the same number the block-at-a-time packing did, bit for bit,
or every chunk statement after it reads the wrong slots. The reference below is that earlier
shape, parameterised by the block size it used, and the checks run it at 256 and at a couple of
others, since the new packing should not depend on the block size at all. -/

/-- The earlier packing: records set into a block in turn, blocks joined at the end. `meta`
because it calls `setBitsLow`, which this file imports for the elaboration phase alone. -/
meta def refRecords (seg k per : Nat) : Nat × Nat := Id.run do
  let slice := (seg >>> (k * 65536)) &&& ((1 <<< 65536) - 1)
  let hits := setBitsLow slice 65536
  let nblk := hits.size / per + 1
  let mut acc : Array Nat := Array.replicate nblk 0
  for j in [0:hits.size] do
    acc := acc.modify (j / per) (· ||| ((hits[j]!) <<< (16 * (j % per))))
  let mut packed := 0
  for j in [0:nblk] do
    packed := packed ||| ((acc[nblk - 1 - j]!) <<< ((nblk - 1 - j) * 16 * per))
  return (packed, hits.size)

/-- A slice with records at awkward counts: one short of a block, one over, and a long run. -/
def seg1 : Nat := ofPositions [0, 1, 2, 5, 9, 17, 64, 65, 1000, 4095, 65534, 65535]

#guard liveRecords 0 0 == refRecords 0 0 256
#guard liveRecords seg1 0 == refRecords seg1 0 256
#guard liveRecords seg1 0 == refRecords seg1 0 4
#guard liveRecords seg1 0 == refRecords seg1 0 512
#guard liveRecords (1 <<< 65535) 0 == refRecords (1 <<< 65535) 0 256
#guard liveRecords ((1 <<< 65536) - 1) 0 == refRecords ((1 <<< 65536) - 1) 0 256
#guard liveRecords ((1 <<< 65536) - 1) 0 == refRecords ((1 <<< 65536) - 1) 0 1024

-- And on a block other than the first, since the caller reads blocks 0 to 50 of the skipped set.
#guard liveRecords (seg1 <<< 65536) 1 == refRecords (seg1 <<< 65536) 1 256
#guard liveRecords (seg1 <<< (3 * 65536)) 3 == refRecords (seg1 <<< (3 * 65536)) 3 256

-- The layout the chunk slicing relies on: record `j` at bit `16 * j`.
#guard ((liveRecords seg1 0).1 >>> 0) &&& 65535 == 0
#guard ((liveRecords seg1 0).1 >>> 48) &&& 65535 == 5
#guard ((liveRecords seg1 0).1 >>> (11 * 16)) &&& 65535 == 65535
#guard (liveRecords seg1 0).2 == 12

/-! ## `stripeSort` against the packing it replaces

`stripeSort` is the production marking route's own emitter path, so its four returned numbers have
to come back bit for bit identical. The reference below is the shape before the pairwise packing
went in: each record set into a growing slot, each slot into a growing list, each slice's assembly
into a growing mask. -/

/-- The earlier packing, kept to compare against. `meta` for the reason `refRecords` is. -/
meta def refStripeSort (s lo Wm1 start len W nrec : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 65536
  let mut slots : Array (Array Nat) := Array.replicate (np + 1) #[]
  let mut slotAsm : Array Nat := Array.replicate np 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:nrec] do
      let X := (if w &&& 1 = 0 then b5 else b7) + (w >>> 1) * d
      if X ≤ Wm1 then
        slots := slots.modify (X >>> 16) (·.push (8 * i + w))
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
      else
        slots := slots.modify np (·.push (8 * i + w))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  let mut seen := 0
  for w in [0:nrec] do
    seen := seen ||| (c <<< (w * len))
  let mut slotW := 16
  for k in [0:np + 1] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np + 1] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

/-- A divisor set with bits spread across a batch, including the first and last positions. -/
def divisors : Nat := ofPositions [1, 2, 3, 5, 8, 13, 21, 34, 55, 63]

-- One slice, the shape most batches take.
#guard stripeSort divisors 0 65535 1 64 65536 4 == refStripeSort divisors 0 65535 1 64 65536 4
#guard stripeSort divisors 0 65535 1 64 65536 2 == refStripeSort divisors 0 65535 1 64 65536 2
#guard stripeSort divisors 0 65535 1 64 65536 8 == refStripeSort divisors 0 65535 1 64 65536 8

-- Several slices, so the list and the assembly both have more than one slot to join.
#guard stripeSort divisors 0 262143 1 64 262144 4
  == refStripeSort divisors 0 262143 1 64 262144 4
#guard stripeSort divisors 0 262143 1 64 262144 8
  == refStripeSort divisors 0 262143 1 64 262144 8

-- A window start other than zero, which moves every seed.
#guard stripeSort divisors 1000 65535 1 64 65536 4
  == refStripeSort divisors 1000 65535 1 64 65536 4
#guard stripeSort divisors 100000 262143 1 64 262144 4
  == refStripeSort divisors 100000 262143 1 64 262144 4

-- An empty batch, where every slot is empty and the odd-element carry never happens.
#guard stripeSort 0 0 65535 1 64 65536 4 == refStripeSort 0 0 65535 1 64 65536 4

-- A batch where every position is a divisor, so slots are full and the carry happens at every
-- level with an odd count.
#guard stripeSort ((1 <<< 65) - 1) 0 65535 1 64 65536 4
  == refStripeSort ((1 <<< 65) - 1) 0 65535 1 64 65536 4
#guard stripeSort ((1 <<< 65) - 1) 0 262143 1 64 262144 6
  == refStripeSort ((1 <<< 65) - 1) 0 262143 1 64 262144 6

-- Odd counts specifically, where an element is carried rather than paired.
#guard stripeSort (ofPositions [1, 2, 3]) 0 65535 1 64 65536 4
  == refStripeSort (ofPositions [1, 2, 3]) 0 65535 1 64 65536 4
#guard stripeSort (ofPositions [1, 2, 3, 4, 5]) 0 65535 1 64 65536 3
  == refStripeSort (ofPositions [1, 2, 3, 4, 5]) 0 65535 1 64 65536 3

/-! ## The variants with the other loop bound

`stripeSortW` and `stripeSortG` run their joins over `np` slices rather than `np + 1`, and
accumulate `seen` inside the main loop rather than repeating the slice. Those are the two places
the conversion could have gone wrong in a way the `stripeSort` checks would not catch, so they get
their own reference. -/

/-- `stripeSortW` before the pairwise packing. -/
meta def refStripeSortW (s lo Wm1 start len W nrec : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 65536
  let mut slots : Array (Array Nat) := Array.replicate np #[]
  let mut slotAsm : Array Nat := Array.replicate np 0
  let mut seen := 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:nrec] do
      let X := (if w &&& 1 = 0 then b5 else b7) + (w >>> 1) * d
      if X ≤ Wm1 then
        slots := slots.modify (X >>> 16) (·.push (8 * i + w))
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
        seen := seen ||| (1 <<< (i + w * len))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  let mut slotW := 16
  for k in [0:np] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

#guard stripeSortW divisors 0 65535 1 64 65536 4
  == refStripeSortW divisors 0 65535 1 64 65536 4
#guard stripeSortW divisors 0 262143 1 64 262144 4
  == refStripeSortW divisors 0 262143 1 64 262144 4
#guard stripeSortW divisors 1000 262143 1 64 262144 8
  == refStripeSortW divisors 1000 262143 1 64 262144 8
#guard stripeSortW 0 0 65535 1 64 65536 4 == refStripeSortW 0 0 65535 1 64 65536 4
#guard stripeSortW ((1 <<< 65) - 1) 0 262143 1 64 262144 6
  == refStripeSortW ((1 <<< 65) - 1) 0 262143 1 64 262144 6
#guard stripeSortW (ofPositions [1, 2, 3]) 0 65535 1 64 65536 3
  == refStripeSortW (ofPositions [1, 2, 3]) 0 65535 1 64 65536 3

end PrimeCert.SegTune.SetBitsProbe
