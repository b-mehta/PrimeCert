/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The eight-a-leaf skipped side with a chunk of 2048

`ZZCL_Join1e16Oct` at chunk 2048 instead of 1024.

The chunk was swept with the four-a-leaf tree, where 1024 won on kernel time and each doubling
bought peak at its expense. The leaves are twice as wide now, so a chunk holds half as many of
them and the trade is not the one that sweep measured.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCM_Join1e16OctChunk2048

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 20107203 10000000000000001 4194304 33333333 65536 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZCM_Join1e16OctChunk2048
