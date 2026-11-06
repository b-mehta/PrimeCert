/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One arm of the declaration-name control

`Z1_NameA` and `Z1_NameB` are identical to the byte except for the two digits naming the mode, so
the declarations they emit carry the same names at the same file positions. Mode 28 takes the
window after each batch from that batch's mask and mode 55 recomputes it by marking. Those two
emit the same certificate, yet measured in separate files they differed by about 7 percent of
kernel, which this pair is built to isolate. -/

namespace PrimeCert.SegTune.ZCmp

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.ZCmp
