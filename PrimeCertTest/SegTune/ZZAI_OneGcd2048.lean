/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The chunk doubled once more, with one gcd

`parts 4035`: a chunk of 2048 records and one gcd for the window, which is the top of the chunk
field.

256 to 512 to 1024 has won every time, so the trade has not turned yet and the only way to find
where it does is to pass it. This asks that question in the shape the certificate now has rather
than in the shape it had, since the per-chunk gcds that the chunk size was mostly trading against
are gone.

If this wins too, the field needs another digit before the question can be asked again, and that
is worth doing only if the margin is still worth having.

Pair with `ZZAH_OneGcd1024`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAI_OneGcd2048

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 4035 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAI_OneGcd2048
