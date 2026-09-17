/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The window sieve at 1048576 candidates

The range ladder only ever widened from 4194304, and every step made the cost per candidate worse,
so this asks the question the ladder never did: whether narrowing helps. Mode 16 throughout. -/

namespace PrimeCert.SegTune.N1M_M16

run_sieve 10000000

run_segment_variant 16 100000000000001 1048576 3333332 1536 10000000

end PrimeCert.SegTune.N1M_M16
