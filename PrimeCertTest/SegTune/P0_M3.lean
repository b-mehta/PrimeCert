/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One billion-run segment through mode 3

`P0_M0`'s window with the doubling rounds taken from the window width instead of a fixed 32, wide
primes skipped, and each batch reading its own slice of the base sieve. -/

namespace PrimeCert.SegTune.P0_M3

run_segment_variant 3 100000001 262144 10573 1536

end PrimeCert.SegTune.P0_M3
