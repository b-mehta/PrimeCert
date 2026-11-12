/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Do sixteen records a divisor name the strikes they claim to

Modes 79 and 78 on a narrow window, over the octave where a divisor's eightfold fits the window and
its sixteenfold does not. Mode 78 sorts the band's strikes into slices with a four-bit lane in each
record; mode 79 marks the same divisors the way the sieve does today.

Elaborating mode 78 is itself the check. The emitter states what the kernel's fold should reach and
closes it by reflection, so a record the kernel decodes differently from the way the emitter packed
it fails here rather than going quietly into a timing run. The tally lemma is the other half: it
asks for all sixteen lanes of every divisor in the batch, which is what stops one being left out.
Throwaway. -/

namespace PrimeCert.SegTune.ZZU_Lane16Smoke

run_segment_variant 79 100000000000001 262144 20000 4096

run_segment_variant 78 100000000000001 262144 20000 4096

end PrimeCert.SegTune.ZZU_Lane16Smoke
