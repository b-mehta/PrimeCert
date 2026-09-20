/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # `S7_Sched` at the harmonic record's own parameters

The same mode 20 segment loop as `S7_Sched`, but at the parameters the sum of 1/p runs at: a
segment of 1048576 positions from `1005969665`, divisors to `110017`, which is a twelfth of the
positions and a hundredth of the divisor bound. Sieving only, with none of the summing, so that
the emitter work common to both sessions can be read off on its own. The `common` job times this
beside `S7_Sched`, `S9_Stripes` and `GapW1048` in one job, since runner spread reaches a third.
-/

namespace PrimeCert.SegTune.S7_Mine

run_segment_variant 20 1005969665 1048576 36672 1536 2000000

end PrimeCert.SegTune.S7_Mine
