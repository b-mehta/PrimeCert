/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One billion-run segment, as `run_harmonic_series` emits it today

The window, divisor bound and batch of `Billion/Part00`, sieved by `run_segment`, which is what the
harmonic command calls. `P0_M16` is the same window through mode 16. -/

namespace PrimeCert.SegTune.P0_M0

run_segment 100000001 262144 10573 1536

end PrimeCert.SegTune.P0_M0
