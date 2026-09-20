/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # `S7_Mine` with a third of the divisors, the width held

The breakdown of a segment into kernel, `addDecl` and the rest left the rest flat to 21 percent
per divisor across two parameter sets and out by three to thirteen times per position, per batch
and per strike. Two points cannot tell "per divisor" from anything else that tracks the divisor
count over that range, so these two files add a third and a fourth at one width and one start,
with only the divisor bound moving: `31627` here and `1000003` in `S7_High`, against the `110017`
of `S7_Mine`, which is 3400, 78498 and 10452 divisors at 1048576 positions throughout.
-/

namespace PrimeCert.SegTune.S7_Low

run_segment_variant 20 1005969665 1048576 10542 1536

end PrimeCert.SegTune.S7_Low
