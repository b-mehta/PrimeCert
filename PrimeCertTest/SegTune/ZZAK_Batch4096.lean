/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The batch length re-asked, below 8192

`ZZAH_OneGcd1024` with `len` 4096 instead of 8192. The other side of the bracket from
`ZZAJ_Batch16384`; the reasoning is there.

Both points at once rather than one, because a single point either side of a settled optimum says
only that the optimum moved or did not, while the pair says which way.

Pair with `ZZAH_OneGcd1024` and `ZZAJ_Batch16384`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAK_Batch4096

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3523 100000000000001 4194304 3333333 4096 0 65536 10000000

end PrimeCert.SegTune.ZZAK_Batch4096
