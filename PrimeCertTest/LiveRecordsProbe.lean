/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import SieveEmit.Core

/-! # Does `liveRecords` pack what it claims

It imports `SieveEmit` and nothing else, so it builds in seconds and can be checked on a box that
cannot compile `PrimeCert.SegmentedSieve`. The packing is the part worth checking by example rather
than by eye: a record is sixteen bits, the blocks are joined in descending order, and an
off-by-one in either would be invisible in a docstring and obvious here.

Throwaway. -/

open SieveEmit

-- Bits 0, 1 and 3 of slice 0, so three records holding 0, 1 and 3.
#guard (liveRecords 0b1011 0).2 = 3
#guard (liveRecords 0b1011 0).1 = 0 ||| (1 <<< 16) ||| (3 <<< 32)

-- Nothing live is no records.
#guard (liveRecords 0 0) = (0, 0)
#guard (liveRecords 0b1011 1) = (0, 0)

-- A position at the top of the slice, 65535, still fits one record.
#guard (liveRecords (1 <<< 65535) 0) = (65535, 1)

-- Slice 1 reads the second 65536 bits and reports positions relative to the slice.
#guard (liveRecords (1 <<< 65536) 1) = (0, 1)
#guard (liveRecords (1 <<< 65540) 1) = (4, 1)

-- It reads the set bits of the k-th 65536-bit block of whatever it is given, so the same function
-- serves the skipped-divisor bitmask as well as a window slice: block j there covers divisor
-- indices j * 65536 upwards, and 3333333 of them is 51 blocks. Checked on divisor indices rather
-- than bit positions so the dual use is not just asserted in a docstring.
#guard (liveRecords ((1 <<< 70000) ||| (1 <<< 70003)) 1) = (4464 ||| (4467 <<< 16), 2)
#guard (liveRecords ((1 <<< 70000) ||| (1 <<< 70003)) 0) = (0, 0)

-- Across a block boundary: 257 live positions, the 257th landing in the second block of 256.
#guard (liveRecords ((1 <<< 257) - 1) 0).2 = 257
#guard ((liveRecords ((1 <<< 257) - 1) 0).1 >>> (16 * 256)) &&& 65535 = 256
#guard ((liveRecords ((1 <<< 257) - 1) 0).1 >>> (16 * 255)) &&& 65535 = 255
