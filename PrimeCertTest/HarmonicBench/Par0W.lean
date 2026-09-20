/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The position-walk twin of `Par0`, for the four-at-once comparison

Alone, a segment summed by walking the gaps between its primes took 14.0 s of wall against 20.5 s
for one summed by walking every position, but the gap walk moves work from the kernel to the
elaborator, and four files on one runner share four cores. These four files repeat `Par0` to
`Par3` with the position walk so the two shapes can be timed against each other under that load.
`Par1W`, `Par2W` and `Par3W` carry the next three stretches.
-/

namespace PrimeCert.Par0W

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 48 7

end PrimeCert.Par0W
