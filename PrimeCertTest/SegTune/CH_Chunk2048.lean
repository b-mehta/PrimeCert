/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Records a chunk: 2048

`CH_Chunk256` with `(parts / 512) % 4` at 3, so `parts 53187`.

Pair with `CH_Chunk256`, `CH_Chunk512` and `CH_Chunk1024`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.CH_Chunk2048

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 53187 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.CH_Chunk2048

