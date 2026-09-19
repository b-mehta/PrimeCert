/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sorted run with longer batches over the large primes

`S9_Stripes` with the batches over the primes past half the segment holding 4096 positions rather
than 3072. An entry names a position in 13 bits, so 4096 is the longest such batch this packing
allows. -/

namespace PrimeCert.SegTune.S9_Tail4096

run_sieve 10000000

run_segment_variant 28 100000000000001 4194304 3333332 4096 10000000

end PrimeCert.SegTune.S9_Tail4096
