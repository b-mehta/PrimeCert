/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Records a chunk: 256

`ZZBB_Target1e16Skip` with `(parts / 512) % 4` at 0, so `parts 51651`. Every other flag is the
settled one; only the chunk size moves.

The group this is aimed at is `skipAsm_`, which states `asmChunkK recs cnt d 0 = asm`: a tree of
depth `d` over the chunk's records whose every leaf is `Nat.shiftLeft 1 pos` with `pos` below
65536, combined by `Nat.lor`. A chunk of 1024 records is a tree of 1023 such combinations. At
`10^16` that group is 48.5 of the certificate's 127.7 kernel seconds, which nobody knew until the
certificate was reported in its parts.

Pair with `CH_Chunk512`, `CH_Chunk1024` and `CH_Chunk2048`, one job.

Throwaway. -/

namespace PrimeCert.SegTune.CH_Chunk256

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 51651 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.CH_Chunk256
