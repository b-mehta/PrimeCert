/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The fifth of five consecutive segments run at once

The stretch after `S9_Par4`. Four at once held 9.31 GB summed, so five is worth asking about: a
runner dies above about 14 GB, and more at once is what the whole computation is priced in. -/

namespace PrimeCert.SegTune.S9_Par5

run_sieve 10000000

run_segment_variant 28 100000050331649 4194304 3333332 8192 10000000

end PrimeCert.SegTune.S9_Par5
