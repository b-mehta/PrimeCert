/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The assembly statement folded into the cover step

`parts 7619`: `ZZAH_OneGcd1024` with each chunk's assembly stated inside its cover step rather
than beside it.

The record statements are what is left of the arm's own cost: about 24 s between the two sides,
against a route whose emitter work both arms share. A chunk currently gets two statements, one
saying what its records assemble to and one joining that to the running union. The second already
names the first's result, so the first can go: state `lor acc (asmChunkK …) = next` and the
literal in between is never written.

That drops one statement and one 65536-bit literal a chunk on each side, about 800 statements and
6.5 MB of literals. The kernel reduces the same `asmChunkK` either way, so what is saved is the
writing and the checking of the literal, not the reduction.

Soundness is unchanged and slightly more direct. From `lor acc (asmChunkK …) = next`, a bit of
`next` is a bit of `acc` or a bit of `asmChunkK …`, and the second is already the hypothesis
`not_dvd_of_one_gcd` wants; the separate literal was only a step on the way to it.

Pair with `ZZAH_OneGcd1024`, one job, alternating, peak each. The figures to watch are the
`statements` and `everything else` lines, which is where the saving would show.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAL_MergedCover

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 7619 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAL_MergedCover
