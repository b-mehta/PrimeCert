/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted band as it stands

Mode 34 over the band where a divisor strikes up to four times per progression, which is the band
the sorted records already serve and which took 28.5 of a window's 79.2 kernel seconds. Each
record recomputes the divisor it names and the stride it steps by. `ZC_Forced` states the same
literals with those quantities named by value instead, so the pair prices the recomputation on its
own. Run them alternated on one machine and compare kernel seconds.

The same question was asked once before through `let`, as mode 37, and read as nothing. The
kernel substitutes a `let` rather than evaluating it, so both forms reduced through the same
terms; `ZC_Forced` forces the value instead. -/

namespace PrimeCert.SegTune.ZB_Record

run_sieve 10000000

run_segment_variant 34 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZB_Record
