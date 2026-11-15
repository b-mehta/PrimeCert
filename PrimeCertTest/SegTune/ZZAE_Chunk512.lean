/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same certificate at 512 records a chunk

`parts 963`, which is `ZZAD_SkipCover`'s 451 plus 512: everything the chain needs, with chunks of
512 records at depth 9 instead of 256 at depth 8.

Every arm so far has used 256 without that number being measured against anything. Doubling it
halves the statement count on both record sides, from 1555 and 1717 to about 780 and 860, and
doubles the records each statement carries, so the two move against each other and the kernel's
answer is not something to guess at.

The chunk size has to agree with how the records were packed, so `liveRecords` takes it as a
parameter now rather than holding 256 as a constant.

Pair with `ZZAD_SkipCover`, one job, alternating, peak each. If 512 wins, `parts 1024` is the same
case at 1024 and worth a third point before settling.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAE_Chunk512

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 963 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAE_Chunk512
