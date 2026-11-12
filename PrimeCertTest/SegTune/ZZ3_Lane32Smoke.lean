/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Do thirty-two records a divisor name the strikes they claim to

Modes 81 and 80 on a narrow window, over the octave where a divisor's sixteenfold fits the window
and its thirty-twofold does not. Elaborating mode 80 is the check: the emitter states what the
kernel's fold should reach and closes it by reflection, so a record the kernel decodes differently
from the way the emitter packed it fails here rather than in a timing run. Throwaway. -/

namespace PrimeCert.SegTune.ZZ3_Lane32Smoke

run_segment_variant 81 100000000000001 262144 20000 2048

run_segment_variant 80 100000000000001 262144 20000 2048

end PrimeCert.SegTune.ZZ3_Lane32Smoke
