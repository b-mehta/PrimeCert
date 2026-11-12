/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does the split window sieve what the plain one sieves

Mode 18 and mode 77 on a narrow window. Mode 77 holds the window with its even positions in the
low half and its odd ones in the high half, and marks both halves with one comb of stride `p`.
The emitter unsplits its result after every batch and refuses to emit unless it matches the plain
window exactly, so this passing checks the whole construction: that each progression really does
stay in one half, that halving the starts gives the right offsets, and that the comb lands where
it should. Throwaway. -/

namespace PrimeCert.SegTune.ZZT_SplitSmoke

run_segment_variant 18 100000000000001 262144 20000 4096

run_segment_variant 77 100000000000001 262144 20000 4096

end PrimeCert.SegTune.ZZT_SplitSmoke
