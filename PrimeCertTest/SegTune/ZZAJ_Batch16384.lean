/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The batch length re-asked, above 8192

`ZZAH_OneGcd1024` with `len` 16384 instead of 8192.

8192 was settled with losses either side, but that was against the full divisor set. The route now
runs over the marked subset, which is a quarter of it and scattered differently, and the same `len`
also sets the marking pass's batch. Whether the old optimum survives that change is a question the
old measurement cannot answer.

The marking route is the largest single block of kernel time left — far larger than the whole
certificate — so a few per cent here is worth more than a good result anywhere in the certificate.

Pair with `ZZAH_OneGcd1024` and `ZZAK_Batch4096`, one job, alternating, peak each: the two
together bracket 8192, and if either wins the next point goes further that way.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAJ_Batch16384

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3523 100000000000001 4194304 3333333 16384 0 65536 10000000

end PrimeCert.SegTune.ZZAJ_Batch16384
