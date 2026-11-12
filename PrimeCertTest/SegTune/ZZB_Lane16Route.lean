/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCertTest.LaneChain

/-! # Does the sixteen-record band close a real run

Mode 82 is mode 28 with one more sorted band: the octave where a divisor's eightfold fits the
window and its sixteenfold does not, at sixteen records a divisor rather than a mask. A narrow
window, so that the band is reached and the whole chain is exercised cheaply.

Elaborating this is the check. Every batch of that band is closed by `stripeStepBand16`, whose
hypotheses the kernel settles by reflection, so a record the emitter packed differently from the
way the kernel reads it, or a tally that does not account for all sixteen lanes, fails here.

`PrimeCertTest.LaneChain` is imported because that is where `stripeStepBand16` lives; the emitter
says so by name if it is missing. Throwaway. -/

namespace PrimeCert.SegTune.ZZB_Lane16Route

run_segment_variant 82 100000000000001 262144 20000 2048 1000000

end PrimeCert.SegTune.ZZB_Lane16Route
