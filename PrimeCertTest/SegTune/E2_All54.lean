/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole segment with every band through a 262144-bit-leaf tree

`E2_Rec2` settles every band by sorted records. This settles all three by `wtreeStep2`,
`wtreeStep4` and `wtreeStep8`, so no batch of the run carries a record list, a tally or a separate
clear. Both files emit a certificate for the same segment. -/

namespace PrimeCert.SegTune.E2_All54

run_sieve 10000000

run_segment_variant 54 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E2_All54
