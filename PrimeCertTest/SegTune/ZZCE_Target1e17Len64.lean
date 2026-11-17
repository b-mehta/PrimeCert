/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The proved window at `10^17`, over a base built in batches of 64

`ZZBP_Target1e17Skip` with one character's difference: the base sieve's batch length, 64 instead
of the default 16. Alone, that base went from 6707116 to 5737748 KiB for the same kernel time, and
it stands for 6.5 GiB of the 10982212 KiB a whole window at this depth peaks at. What that is
worth to the run, rather than to the base alone, is what this pair says.

Nothing else moves: same `parts 3329987`, same window, same `#print axioms`.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCE_Target1e17Len64

run_sieve 316300000 64

set_option maxRecDepth 1000000 in
run_segment_skip_part 3329987 100000000000000001 4194304 105433333 65536 0 65536 316300000

#print axioms segEqAll_100000000000000001_4194304_105433333

end PrimeCert.SegTune.ZZCE_Target1e17Len64
