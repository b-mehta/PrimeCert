/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^6`: mode 0 (the current loop), second copy

The same case as `V6_M0a`, run as its own arm so the spread between two copies of the baseline
is measured on the same machine. -/

namespace PrimeCert.SegTune.V6_M0b

run_segment_variant 0 10000000000000001 4194304 333333 512

end PrimeCert.SegTune.V6_M0b
