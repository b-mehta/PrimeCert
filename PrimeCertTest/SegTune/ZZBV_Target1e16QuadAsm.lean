/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The assembly four records a leaf as well

`ZZBU_Target1e16Quad` with `(parts / 2097152) % 2` on, so `parts 3198403`: the chunk products are
stated as `prodQuadK` and the chunk assemblies as `asmQuadK`, both four records a leaf.

`ZZBU` is the arm to read this against, since it already carries the wide products. The difference
between the two is the assembly and nothing else, so `cover asm` is the row that answers it. At
`10^16` that group was 48.5 of the certificate's 127.7 kernel seconds before either change.

The wide assembly reads every slot of a full chunk, which is sound because a part-full chunk is
padded with copies of its last record and a repeated bit ors to itself.
`asmQuadK_eq_asmChunkK` carries it to the narrow tree two levels deeper and `bitsDvd_chunkQA`
consumes it, so nothing downstream changes.

Pair with `ZZBU_Target1e16Quad`, one job, alternating.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBV_Target1e16QuadAsm

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3198403 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.ZZBV_Target1e16QuadAsm
