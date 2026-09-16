/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Variant timing, divisors up to `10^7`: mode 0 (the current loop), first copy

Builds the sieve to `10^7` (`S7_Sieve` times that alone), then one window of 4194304 bits from
`10^14 + 1`, sieved by the divisors at wheel positions `1 … 3333332`, in batches of 1536 steps
(2171 batch lemmas). -/

namespace PrimeCert.SegTune.V7_M0a

run_sieve 10000000

run_segment_variant 0 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.V7_M0a
