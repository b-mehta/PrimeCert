/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same certificate at 1024 records a chunk

`parts 1987`: `ZZAE_Chunk512` with the chunk doubled again, depth 10 instead of 9.

512 beat 256 on all three figures at once, kernel -7.3 s, processor -7.3 s and peak -65 MB, which
settles nothing about where the trade turns. This is the third point. Fewer, fatter statements
keep winning until the literals a statement carries outgrow what is saved by not having a
statement at all, and the only way to find that is to pass it.

Written up here because goldbach generated the same arm on the box to get the 1024 point in one
job; this is that case in the repository so the arm is not lost with the box.

Pair with `ZZAE_Chunk512` and `ZZH_FullWindow28`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAF_Chunk1024

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 1987 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAF_Chunk1024
