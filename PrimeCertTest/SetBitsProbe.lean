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

end PrimeCert.SegTune.SetBitsProbe
