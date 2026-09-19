/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A segment at `10 ^ 9` with the two changes a record attempt would adopt

Twice the width of `Ht09`, 524288 positions, and the count of primes bounded by that width so
only one quantity is summed. The divisors reach 100003 rather than 31637, which is what a run
covering up to about `7 * 10 ^ 9` needs. Costs are compared per integer covered, since this
segment covers twice as many as `Ht09` does.
-/

namespace PrimeCert.Ht09_F7W2

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 524288 100003 20 2048 1536 1 7

end PrimeCert.Ht09_F7W2
