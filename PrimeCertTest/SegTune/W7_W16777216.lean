/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Segment timing: divisors up to `10^7`, segment 16777216 bits, batches of 2048 steps

Builds the sieve to `10^7` (`S7_Sieve` times that alone), then one segment of 16777216 bits
starting at `10^14 + 1`, sieved by the divisors at wheel positions `1 … 3333332` (the numbers up
to `9999997`), in batches of 2048 steps (1628 batch lemmas). -/

namespace PrimeCert.SegTune.W7_W16777216

run_sieve 10000000

run_segment 100000000000001 16777216 3333332 2048 10000000

end PrimeCert.SegTune.W7_W16777216
