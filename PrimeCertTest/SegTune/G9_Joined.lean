/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The divisors that strike the segment many times, joined into one mask a batch

Four times one of these divisors still fits inside the segment, so each strikes it many times and
sorting the strikes does not apply. Here a batch's masks are joined into one and the segment is
cleared against that once, rather than once per divisor. Joining lost by 2.6 times when it was
tried over every divisor, where it paid doubling rounds on the large ones that marking skips
outright; over these divisors there are no such rounds to pay. `G8_Marked` is the same divisors
marked the way the sieve does today. -/

namespace PrimeCert.SegTune.G9_Joined

run_sieve 10000000

run_segment_variant 32 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.G9_Joined
