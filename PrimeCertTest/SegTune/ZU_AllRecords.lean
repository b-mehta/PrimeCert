/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted band with every record kept

Mode 34 over the band where a divisor strikes up to four times per progression. Every divisor gets
eight records whether or not its strike lands inside the window, and the tally asks for all eight,
which is what stops a divisor being skipped. Counted over the divisors a 1..10^12 window is given,
28.6 percent of those records name a strike past the end of the window.

`ZV_WindowRecords` drops exactly those, so the pair bounds what the sound version could save. The
sound version is not this: it needs a flag bit in the record to keep the tally honest, which makes
the record 1 + 3 + 12 bits and caps a batch at 4096 positions, where the length is tuned to 8192.
Measure the ceiling first and design that only if the ceiling is worth it. -/

namespace PrimeCert.SegTune.ZU_AllRecords

run_segment_variant 34 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZU_AllRecords
