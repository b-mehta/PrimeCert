/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The skip records covering the skipped set

`parts 451`, which is `ZZAC_Cover`'s 195 plus 256: the cover on the skipped side as well.

`ZZAC` ties the live records to the window. The skipped side has the same hole and it matters more:
a divisor left out of the skip records would be dropped from the marking and left out of the
product, so nothing would divide anything and the gcd would pass for the wrong reason. The cover
closes it against `skipSet_…`, the literal the emitter already names, so the records are tied to
the set the route was allowed to leave out.

51 blocks here against the window's 64 slices, and 1717 chain steps against the live side's 1555,
so this should land near `ZZAC`'s cost rather than above it. Both figures are a guess until the
pair runs.

Pair with `ZZAC_Cover`, one job, alternating, peak each.

With this arm in, every literal the certificate rests on is said rather than asserted, bar the
window itself, which the route proves.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAD_SkipCover

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 451 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAD_SkipCover
