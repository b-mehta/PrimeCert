/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The window after a batch, found through a byte array

The other arm of the pair described in `Z2_MaskTwin`. Mode 66 is mode 28 with the twin reaching
the next window through a byte array, one bit set per strike, joined once a batch, rather than
through a mask built and subtracted per divisor. If the two arms disagreed by a single bit the
kernel check would fail and the run would go red, so a green pair is also a check that they
agree. -/

namespace PrimeCert.SegTune.Z3_BytesTwin

run_sieve 10000000

run_segment_variant 66 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.Z3_BytesTwin
