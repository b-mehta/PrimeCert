/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: mode 16

`V7_M11` with each batch joining its primes' crossing-out patterns into one and the window cleared
against the total once at the end, in place of once per prime. Same slices, same twin, same chain,
so `V7_M11` is the arm to compare it against. -/

namespace PrimeCert.SegTune.V7_M16

run_sieve 10000000

run_segment_variant 16 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.V7_M16
