/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The chunks covering the window

`parts 195`, which is `ZZAB_SkipProduct`'s 67 plus 128: the same arm with the cover stated.

Every chunk statement so far is about some 256 records. Nothing yet says those records exhaust the
window's live bits, so a chunk left out would pass unnoticed and the certificate would certify a
subset of the window while reading as though it covered all of it. The cover closes that: a
slice's chunk assemblies are `lor`ed together a step at a time, each step a statement, and the
slice they reach is checked against the window shifted down and masked.

The second half is stated against the name the route gave the window, not against a fresh literal
with the same digits, so it is about the definition the rest of the chain is about.

The cost question is the slice statements, 64 of them, each shifting a 4-Mbit literal down and
masking 65536 bits off it. The chain steps are `lor`s of 65536-bit literals and should be the
cheaper half, but neither has been measured.

Pair with `ZZAB_SkipProduct`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAC_Cover

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 195 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAC_Cover
