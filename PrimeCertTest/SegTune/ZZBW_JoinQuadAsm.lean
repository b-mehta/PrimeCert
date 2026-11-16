/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window with both chunk trees wide

`ZZBM_JoinProved` with the two wide-leaf bits on, so `parts 3329475`: chunk products as
`prodQuadK`, chunk assemblies as `asmQuadK`, and the per-window theorem emitted with its proof.

This is the case that checks the join against the wide assembly, which a build cannot: the emitter
compiles whatever it builds, and whether the proof term typechecks is only decided when a window
runs. The join reaches the wide assembly through `bitsDvd_chunkQA`, with the chunk's `cnt` taken
as the full chunk because a part-full one is padded.

What to read: that it elaborates at all, and that `#print axioms` names only `propext`,
`Classical.choice` and `Quot.sound`.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBW_JoinQuadAsm

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3329475 100000000000001 4194304 3333333 8192 0 65536 10000000

#print axioms segEqAll_100000000000001_4194304_3333333

end PrimeCert.SegTune.ZZBW_JoinQuadAsm
