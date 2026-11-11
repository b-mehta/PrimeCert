/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A window marked by masks built by doubling

Mode 18 over the divisors a 1..10^12 run needs, each marked by a mask the kernel builds by
doubling its span until a further doubling would pass the window. The span it finishes with lies
between the window's width and twice it, so the last round is the widest write of the lot.
`ZH_ExactSpan` stops the doubling one round earlier and finishes the span with a single shift,
leaving a mask that spans the window and a little over.

Run the two alternated on one machine and compare kernel seconds. Both state the same literals,
and the emitter refuses to emit the narrower one if it clears a different window, so a green pair
also says the two constructions agree. -/

namespace PrimeCert.SegTune.ZG_Doubling

run_sieve 10000000

run_segment_variant 18 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZG_Doubling
