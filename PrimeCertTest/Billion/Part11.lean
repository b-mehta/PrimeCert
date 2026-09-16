/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The primes from `930472193` to `1005969664`

The last of the twelve, so it carries the range past `10 ^ 9`.
-/

namespace PrimeCert.Billion.P11

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 930472193 262144 31627 20 2048 1536 96

end PrimeCert.Billion.P11
