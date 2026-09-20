/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The divisors below a sixteenth of the segment, marked the current way

Stops at wheel index 87381, where a divisor's multiples start landing more than sixteen times.
Subtracting this from `N7_M18c` prices the band a sixteen-record layout would cover, which is what
says whether widening the strike field to four bits is worth the halved batch length. -/

namespace PrimeCert.SegTune.N7_M18d

run_sieve 10000000

run_segment_variant 18 100000000000001 4194304 87381 1536 10000000

end PrimeCert.SegTune.N7_M18d
