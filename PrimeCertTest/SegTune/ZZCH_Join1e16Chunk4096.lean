/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^16` with a chunk of 4096

The long arm of the sweep `ZZCG_Join1e16Chunk2048` describes, and the first reading past the top
of the chunk field: `(parts / 8388608) % 2` doubles whatever the two bits ask for, so 2048 and
that bit give 4096 without renumbering any flag above it.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCH_Join1e16Chunk4096

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 11718595 10000000000000001 4194304 33333333 65536 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZCH_Join1e16Chunk4096
