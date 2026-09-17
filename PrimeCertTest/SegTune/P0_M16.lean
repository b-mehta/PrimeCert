/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One billion-run segment through mode 16

`P0_M0`'s window with each batch joining its primes' crossing-out patterns into one and the window
cleared against the total once, so the pair prices that change for the billion. -/

namespace PrimeCert.SegTune.P0_M16

run_segment_variant 16 100000001 262144 10573 1536

end PrimeCert.SegTune.P0_M16
