/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same certificate, marked the clamped way

Mode 9: the chain plain `run_segment` builds, over the same divisors and the same batch length,
but marking through `segMarkCK` rather than `segMarkK`. The arm to read it against is
`ZZ1_ProdPlain`, where the reasoning for the pair is written out.

Both arms end at `segEqI_` on `segRun`, so whichever wins, a consumer of the sieve sees the same
statement. -/

namespace PrimeCert.SegTune.ZZ2_ProdClamped

run_sieve 10000000

run_segment_variant 9 100000000000001 4194304 333333 512 10000000

end PrimeCert.SegTune.ZZ2_ProdClamped
