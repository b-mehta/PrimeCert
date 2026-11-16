/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Records a chunk: 1024, the settled size

`ZZBB_Target1e16Skip` unchanged, `parts 52675`. The baseline the other three chunk sizes are read
against, carried as its own case so the four rows of the table are alike.

Pair with `CH_Chunk256`, `CH_Chunk512` and `CH_Chunk2048`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.CH_Chunk1024

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 52675 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.CH_Chunk1024
