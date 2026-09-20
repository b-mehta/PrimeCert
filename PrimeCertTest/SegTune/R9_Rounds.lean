/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The many-strike divisors, each batch given only the rounds it needs

A divisor's multiples are written by doubling a pair of seed bits until they span the segment, and
the number of doublings a batch is handed is fixed at what the whole segment needs, 22 here. A
divisor near the top of this band needs one. The rounds beyond what a divisor needs are skipped by
a test rather than performed, so both arms compute the same value, and this file against
`R8_Global` prices those skipped rounds. -/

namespace PrimeCert.SegTune.R9_Rounds

run_sieve 10000000

run_segment_variant 36 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.R9_Rounds
