/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A whole run at twice the segment width, sorted

`S9_Stripes` on a segment of 8388608 positions rather than 4194304, so 128 pieces of 65536 bits
rather than 64. The two cover the same divisors, so the comparison is cost per candidate rather
than cost per segment.

A ladder taken before any of the sorting existed found cost per candidate rising with width, 78.6
microseconds at 4194304 against 103.7 at 8388608, and that is why 4194304 was chosen. The sweep at
one trillion found the opposite direction once sorting applies, so the ladder is worth re-asking on
the current shape. The divisor bound of ten million still clears the square root of this segment's
top.

At a batch of 16384 positions over the large divisors this was killed twice at 14 GB, where the
narrower segment holds 3.5, so the batch length is shortened to 4096 here to separate the width
from the length as the cause. -/

namespace PrimeCert.SegTune.S9_Wide8

run_sieve 10000000

run_segment_variant 28 100000000000001 8388608 3333332 4096 10000000

end PrimeCert.SegTune.S9_Wide8
