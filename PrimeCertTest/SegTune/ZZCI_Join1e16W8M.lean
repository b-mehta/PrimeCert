/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^16`, twice as wide

`ZZBY_Join1e16Quad` with `W` at 8388608 instead of 4194304, so one run covers 25165824 integers
rather than 12582912. The `65536`-bit slice still divides it, 128 times rather than 64.

What a run of this costs matters less than what it costs for each integer it covers, and that is
the figure a wider window moves. `ZZBY` takes 201.512 kernel seconds and 4445480 KiB; twice the
width at less than twice the time is a gain, at more than twice a loss, and the peak has 9.6 GiB
of room either way.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCI_Join1e16W8M

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3329475 10000000000000001 8388608 33333333 65536 0 65536 100000000

#print axioms segEqAll_10000000000000001_8388608_33333333

end PrimeCert.SegTune.ZZCI_Join1e16W8M
