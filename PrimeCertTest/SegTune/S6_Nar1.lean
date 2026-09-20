/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The first of four consecutive half-width segments run at once

The width was settled one segment at a time, and the sieve runs four at once, so nothing has ever
compared the widths in the regime that matters. `S6_Nar1` to `S6_Nar4` are `S9_Par1` to `S9_Par4`
at half the window, covering half the range between them; the comparison is seconds per bit, not
seconds per file. -/

namespace PrimeCert.SegTune.S6_Nar1

run_sieve 10000000

run_segment_variant 28 100000000000001 2097152 3333332 8192 10000000

end PrimeCert.SegTune.S6_Nar1
