/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One window at fuel 10575, a window of 1..10^9, every divisor in the small band, on the plain elaborator -/

namespace PrimeCert.SegTune.YA_Plain

run_sieve 10000000

run_segment 100000000000001 4194304 10575 8192 10000000

end PrimeCert.SegTune.YA_Plain
