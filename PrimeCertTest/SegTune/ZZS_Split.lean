/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A window split by parity, so one comb serves both of a divisor's progressions

A divisor's two progressions both have stride `2p`, and their first positions differ by an odd
number, so one of them lands only on even window positions and the other only on odd ones. Mode 77
holds the window with its evens in the low half and its odds in the high half. In those halves both
progressions have stride `p`, so one comb built to half the window's width serves both: it is
shifted to the even progression's start, and again to the odd one's, each placement clamped to its
own half.

Mode 18 builds a comb to the full width for each progression separately. So the saving to measure
is the construction, and the cost against it is the two clamps, the second shift, and a window
shaped so the final answer has to be put back before anything else reads it.

Pair with `ZG_Doubling`, which is mode 18 over the same divisors. The emitter unsplits mode 77's
window after every batch and refuses to emit unless it matches the plain one, so a green run also
says the construction is right. -/

namespace PrimeCert.SegTune.ZZS_Split

run_sieve 10000000

run_segment_variant 77 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZZS_Split
