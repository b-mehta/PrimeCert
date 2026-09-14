/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark baseline: the `10^8` sieve alone

`run_sieve 100000000` and no segment. This is the baseline the whole comparison is measured
against: case `E_Base1e8` is this row plus one segment, so `E − this` is the segment cost at the
base depth that actually certifies primality below `10^16`.

Not run on the development box. Same standing restriction as `E_Base1e8`.
-/

namespace PrimeCert.SegBench.Base1_Sieve1e8

run_sieve 100000000

end PrimeCert.SegBench.Base1_Sieve1e8
