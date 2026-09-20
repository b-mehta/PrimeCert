/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The eight-strike band assembled from slices of twice the width

Slices of half the width were measured and lost, 2.8 and 3.6 percent of kernel and 6.3 of peak, so
this asks the other direction: 32 slices of 131072 bits rather than 64 of 65536. Same band, same
divisors, same value, so the pair against `E9_Sorted` is the slice width on its own.

I predicted the narrow arm would win and it did not, so I am making no prediction here. -/

namespace PrimeCert.SegTune.E6_Wide

run_sieve 10000000

run_segment_variant 40 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E6_Wide
