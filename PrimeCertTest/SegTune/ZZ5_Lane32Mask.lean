/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same octave, marked the way the sieve marks it today

Mode 81 over the band where a divisor's sixteenfold fits the window and its thirty-twofold does
not, each divisor given a mask built by doubling. This is the arm `ZZ4_Lane32` is measured
against, at the same batch length so the two run over the same divisors in the same groups. -/

namespace PrimeCert.SegTune.ZZ5_Lane32Mask

run_sieve 10000000

run_segment_variant 81 100000000000001 4194304 333333 2048 10000000

end PrimeCert.SegTune.ZZ5_Lane32Mask
