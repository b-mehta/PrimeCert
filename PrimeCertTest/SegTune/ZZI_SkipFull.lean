/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A full window, marking only the divisors that strike something

`run_segment_skip` at the production window, threshold 32768. The counts predict 497131 of 661067
divisors skipped, 90.5% of them in the wide band, and the emitter logs what it actually got.

Pair with `ZZH_FullWindow28`, **both arms in one job**, and report peak for each. The comparison is
whole-window kernel and processor, because this moves work between the batch lemmas and a new row:
the 64 gcd equations, whose names end `skipGcd_`. Read those apart from the batch lemmas, since
the design trades one against the other.

**Read the emitter's own lines too**, which the batch lemmas hide: `skip set: prefix … | test … |
check …`. The test is the per-divisor strike probe and is a real per-window cost the design adds;
the check rebuilds the window from the marked subset and is the emitter verifying itself, so it
would not run in production. On a 65536-bit window the test took 696 ms over 13677 divisors, and
this window is 64 times wider over 48 times as many, so the test is the number most likely to
decide this.

No chain and no soundness: every batch literal and every gcd is kernel-checked, but nothing yet
ties them to `segLoopK`. That proof gets written if this wins.

Throwaway. -/

namespace PrimeCert.SegTune.ZZI_SkipFull

run_sieve 10000000

run_segment_skip 100000000000001 4194304 3333333 8192 32768 10000000

end PrimeCert.SegTune.ZZI_SkipFull
