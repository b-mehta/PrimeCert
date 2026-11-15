/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The production route halfway to the target

`ZZH_FullWindow28` at `10^15 + 1` with divisors to `3.17e7`, just above the square root of the
window top, which is about 3.2 times the divisors of the `10^14` arms at the same width.

Halfway in log scale between where the tuning was measured and where the sieve is aimed. Bhavik
asked for a mini version rather than the full `10^16` pair, which was the right call: it costs a
small fraction and still says which way the advantage moves with depth.

Written up here because goldbach generated it on a box that has since been terminated, from `ZZH`
with only the start, the fuel and the sieve bound changed. Without this file the `10^15` point is
not reproducible.

Pair with `ZZBD_Mid1e15Skip`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBC_Mid1e15Route

run_sieve 31700000

set_option maxRecDepth 1000000 in
run_segment_variant 28 1000000000000001 4194304 10566666 8192 31700000

end PrimeCert.SegTune.ZZBC_Mid1e15Route
