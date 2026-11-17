/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^17`, with the chunk doubled past the field's top

`ZZCE_Target1e17Len64` with `(parts / 8388608) % 2` set, which takes the chunk from 2048 records
to 4096. Everything else is the same, including the base sieve's batch length of 64.

Asked now because of what that length left behind. Of `ZZCE`'s 504.376 kernel seconds the
certificate is 267.8 — skip records 142.791 and the skip cover 124.972, of which the assembly
alone is 120.869 — and the chunk is what sets how many statements carry it. The field stops at
2048, so there was no reading past it; and the trade it makes is statement count against literal
size, which wants memory, of which there is now 6.40 GiB spare where there had been 2.76.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCF_Target1e17Chunk4096

run_sieve 316300000 64

set_option maxRecDepth 1000000 in
run_segment_skip_part 11718595 100000000000000001 4194304 105433333 65536 0 65536 316300000

#print axioms segEqAll_100000000000000001_4194304_105433333

end PrimeCert.SegTune.ZZCF_Target1e17Chunk4096
