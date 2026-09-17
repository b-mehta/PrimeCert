/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # `Bench.H4`'s positions in one wide window

The same 1048576 positions as `Bench.H4`, as a single window rather than four, since narrowing the
window to 65536 cost more than it saved and the scan over base primes is paid once per window. -/

namespace PrimeCert.Bench.B512

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 1048576 31721 20 512 1536 1

end PrimeCert.Bench.B512
