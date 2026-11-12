/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Sorting two octaves further down than the sieve sorts today

Mode 80 over the band where a divisor's sixteenfold fits the window and its thirty-twofold does
not. Thirty-two records name every strike of such a divisor, so the lane takes five bits of a
record and the position eleven, which caps a batch at 2048 divisors.

Pair with `ZZ5_Lane32Mask`. The octave above was measured on 2026-11-12 and sorting won it on all
three figures: kernel 22.59-22.88 s against 25.95-26.25, processor 24.3-24.6 against 38.4-38.9,
peak 1.84 GB against 5.28 (`ZZV_Lane16`). Going down one more octave doubles the records a divisor
owes while what a mask costs does not move with them, so this is where the two should meet. Where
that happens decides how much of the small band the sorted route should take, which is the largest
open question left in the forty seconds of batch lemmas. -/

namespace PrimeCert.SegTune.ZZ4_Lane32

run_sieve 10000000

run_segment_variant 80 100000000000001 4194304 333333 2048 10000000

end PrimeCert.SegTune.ZZ4_Lane32
