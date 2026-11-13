/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same four slices, stated over shorter ones

`ZZG_SkipSlices` keeps the 65536-bit slice the kernel refused and raises the recursion limit. This
takes the other route and shortens the slice to 4096, leaving the limit alone: 64 gcd equations
over this window in place of 4, each a sixteenth as deep.

Run it alongside `ZZG_SkipSlices`. Whichever passes decides the shape the full window is measured
in, and if both pass this is the one to prefer, since it needs no option set. The two are not
equivalent for the measurement: a shorter slice means more gcd equations, so the full window would
carry 1024 rather than 64, and that cost is the thing the pair against `ZZH_FullWindow28` has to
settle rather than assume.

Throwaway. -/

namespace PrimeCert.SegTune.ZZK_SkipSlices4k

run_segment_skip 100000000000001 262144 50000 1024 1024 4096 1000000

end PrimeCert.SegTune.ZZK_SkipSlices4k
