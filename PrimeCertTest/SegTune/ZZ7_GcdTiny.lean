/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A tiny mode 75, to check the runner reports its three timers

`ZZQ_GcdPrice` at a size that fits a small box. It measures nothing worth reading; it exists so
that `run.sh`'s gcd rows can be checked against a real run before a real one is asked for.

It is sized so the three timers read **non-zero**. The first version of this probe was smaller and
every timer read 0 ms, which was taken for "too small to measure" and was really the timers
bracketing a `let` that had not been evaluated yet. A probe whose expected answer is zero cannot
tell the two apart, so this one must print real numbers to have checked anything.

Checked at `W = 524288` over 20000 divisors: window 486 ms, primorial 65 ms, slice products
567 ms against a window command of 1.142 s, so the three account for 98% of it and the summary
row carries all three.

The `segLoopC` timer in the sorted modes is built the same way and was checked at the same time:
it reported 325 ms on a small mode 28 run, so it is reporting real work. In a loop the lagged
evaluation falls inside the next iteration's bracket, so the total survives even though a single
iteration's share may be a step behind. It was the three one-shot timers here, with no next
iteration to fall into, that read zero. Throwaway. -/

namespace PrimeCert.SegTune.ZZ7_GcdTiny

run_segment_variant 75 100000000000001 524288 20000 2048 1000000

end PrimeCert.SegTune.ZZ7_GcdTiny
