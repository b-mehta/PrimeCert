/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same divisors over a window of twice the width

The other arm of the pair described in `WA_Narrow`. The width was measured before at the divisor
count a 1..10^14 run needs, where the band mix is quite different; this asks the question at the
count a 1..10^12 run needs, where every divisor would sit in the small band. This window covers
twice as many integers, so it is compared against twice `WA_Narrow`. -/

namespace PrimeCert.SegTune.WB_Wide

run_sieve 10000000

run_segment_variant 28 100000000000001 8388608 333333 8192 10000000

end PrimeCert.SegTune.WB_Wide
