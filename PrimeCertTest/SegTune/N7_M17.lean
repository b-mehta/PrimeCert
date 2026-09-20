/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Mask width, trimmed: the per-batch checks over the primes below two million

The 456 batches whose primes are small enough that their positions are doubled into place, with the
mask built to the window's own width. No chain and no final theorem, so this times the mask builder
against `N7_M18`, which is the same batches with the mask built as it is today. -/

namespace PrimeCert.SegTune.N7_M17

run_sieve 10000000

run_segment_variant 17 100000000000001 4194304 700416 1536 10000000

end PrimeCert.SegTune.N7_M17
