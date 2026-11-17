/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^16` with a chunk of 2048

`ZZBY_Join1e16Quad` is the same at 1024, which is where the chunk was left as a trade of kernel
time against peak. Both chunk trees are four records a leaf here as there.

The trade is worth asking again because the certificate is the larger half of the kernel and the
chunk sets how many statements carry it. `ZZCH_Join1e16Chunk4096` is the arm past the top of the
two-bit field, which `(parts / 8388608) % 2` reaches by doubling whatever the field asks for.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCG_Join1e16Chunk2048

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3329987 10000000000000001 4194304 33333333 65536 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZCG_Join1e16Chunk2048
