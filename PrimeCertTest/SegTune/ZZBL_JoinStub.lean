/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # What the join costs, before its proof is written

`parts 118211`: the settled shape with the per-window join emitted, and the join's proof left as
a hole.

**This arm certifies nothing.** It states that marking by every divisor gives the same window as
marking by the subset, and does not prove it. Read it for the timing and for nothing else; a run
of it says what the complete design would cost, not that the design is sound.

Why in this order. Everything measured so far emits the route's theorem about the subset plus the
certificate's facts, and never joins them, so a skip-design window is not yet something a consumer
can use. Writing that join properly is proof work. Knowing whether it is worth writing is a
measurement, and the measurement does not need the proof: the statement, the literals and the
split identity are the same either way.

What is real here and what is not. The split identity, that the marked subset and the skipped set
together are the divisor set the route was asked about, is checked by the kernel over two 3.3 Mbit
literals, and is the part that plausibly costs something. The window theorem itself is stated with
a hole. The emitter prints a warning saying so on every run.

Pair with `ZZBK_ShallowBase`, one job, alternating, peak each. The difference is the whole cost of
joining, and the lines to read are `join: split identity … ms, stubbed window theorem … ms`.

Throwaway, and more so than the rest: delete it once the join is proved for real.
-/

namespace PrimeCert.SegTune.ZZBL_JoinStub

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 118211 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZBL_JoinStub
