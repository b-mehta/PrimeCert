/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One window of the 1..10^9 range, alone in its file

Window 79, the last of the range `X1_Range1e9` covers, emitted on its own. Against
`X3_Twenty` and `X1_Range1e9`, which hold twenty and seventy-nine windows, this says
whether a window costs more when it shares a file with others. -/

namespace PrimeCert.SegTune.X2_One

run_sieve 10000000

run_segment 994050049 4194304 10575 8192 10000000

end PrimeCert.SegTune.X2_One
