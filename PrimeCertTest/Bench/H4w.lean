/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # `Bench.H4`'s positions in narrower windows

The same 1048576 positions as `Bench.H4`, as sixteen windows of 65536 rather than four of 262144,
to price the width of the sieve's operands against their number. -/

namespace PrimeCert.Bench.H4w

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 100000001 65536 31721 20 2048 1536 16

end PrimeCert.Bench.H4w
