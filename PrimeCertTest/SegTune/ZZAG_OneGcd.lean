/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # One gcd for the window instead of one a chunk

`parts 3011`: `ZZAE_Chunk512` with the certificate's shape changed rather than its chunk size.

Every arm so far takes one gcd a chunk against the skipped product, so the skipped product is read
once a chunk, 787 times. This states each chunk's product as a literal instead, combines them
pairwise into the window's product the way the skipped side already is, and takes a single gcd of
the two.

What it trades is 787 gcds for 786 multiplications and one gcd of two large numbers. Which side of
that is cheaper is not something to reason about from here, and the skipped side's chain came in
at +10.3 s for 1717 chunks, which prices the multiplications but says nothing about the gcd.

The soundness is unchanged: a chunk's product divides the window's product, so a live value
divides it too, and the single gcd rules out a shared factor exactly as the per-chunk ones did.

Pair with `ZZAE_Chunk512`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAG_OneGcd

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3011 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAG_OneGcd
