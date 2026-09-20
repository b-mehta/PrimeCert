/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A segment summed in batches of 512 positions

The emitter builds `(W + batch - 1) / batch` summing batches and one declaration for each, so at
512 positions a segment of 1048576 emits 2048 of them. These five files move that count by sixteen
times with everything else held, which is what the `Len*` files were meant to do and did not: they
moved the sieve's batch length instead and every one of them emitted the same 2775 entries.
-/

namespace PrimeCert.Sum0512

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 512 1536 1 15

end PrimeCert.Sum0512
