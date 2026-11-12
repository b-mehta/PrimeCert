/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The top tier moved, checked by count

Mode 83 against `ZZ_TierProbeTop28`; the reasoning is there. Throwaway. -/

namespace PrimeCert.SegTune.ZZ_TierProbeTop83

run_sieve 10000000

run_segment_variant 83 100000000000001 65536 750000 2048 10000000

end PrimeCert.SegTune.ZZ_TierProbeTop83
