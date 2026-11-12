/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The four smallest divisors cleared by one shared mask

Mode 74 is mode 18 with 5, 7, 11 and 13 cleared by a single mask built at their shared period of
10010 positions and tiled to the window, rather than four masks each doubled the whole way. The
emitter refuses to emit unless that mask clears exactly the window the four separate masks clear.

Pair with `ZG_Doubling`, which is mode 18 over the same divisors. Expect nothing: the union of a
set of divisors repeats with period twice their product, which has to fit the window, so only 5,
7, 11, 13, 17 and 19 are ever eligible out of the small band's 43390. The arithmetic puts the
ceiling at a few thousandths of a percent; this is here because a ceiling is not a measurement.

**Measured 2026-11-12, and it is a tie.** Fresh c7i.8xlarge, `run.sh 3`, load about 1: kernel
95.4-95.9 s against Doubling's 95.5-96.3, processor 136.9-137.6 against 136.8-138.3, peak 11.7 GB
either way. Within 0.3% on every figure, which is what the ceiling said. Nothing to land, and
nothing to retry: a shared period only pays where the period fits the window. -/

namespace PrimeCert.SegTune.ZZP_Combo

run_sieve 10000000

run_segment_variant 74 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZZP_Combo
