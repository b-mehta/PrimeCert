/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does the sweep get the window right from the eight-strike band?

`parts 16394`: the sweep starting where `8p` exceeds `Wm1`, so only the masked small band is
marked plainly and everything above it is tested, with the self-check on and nothing else emitted.

This is the deepest the sweep can go: below it is the base it tests against, which cannot test
itself. It is also the setting that exercises the walk hardest, since a divisor here has up to four
strikes a seed where the wide band has one.

It passed at `f2b869b`: `agree true`, with `marked 170768 | skipped 493809 of 621189 |
struck 127380` and the small band's 43388 marked unconditionally. Every one of those four numbers
matches what `scripts/band_skippable.py` counts independently, so the emitter and a brute-force
count of the same window agree to the digit at the most aggressive setting.

Split from `ZZBG_SweepSelfCheck` rather than sharing its file: the emitter truncates its log at the
start of each run, so two runs in one file lose the first's `agree` line.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBH_SweepEightCheck

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 16394 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZBH_SweepEightCheck
