/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A tenth of the divisor range, same window

Measurement only, not a certificate: see `D1_Fuel3333332`. -/

namespace PrimeCert.SegTune.D1_Fuel333333

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.D1_Fuel333333
