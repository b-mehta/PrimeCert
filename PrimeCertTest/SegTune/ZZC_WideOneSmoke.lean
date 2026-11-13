/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does the one-bit lane agree with the kernel

Mode 86 on a small window. Nothing here is timed; this is the correctness check for
`SieveEmit.stripeSortOne` against `stripeBatchLK` at `lw = 1`, and it comes free, because every
literal the emitter produces is checked by the kernel against the definition. A twin that packed a
record wrongly, named the strikes in the other order, or ran the position past fifteen bits would
fail to elaborate here rather than quietly reporting a wrong time later.

No `run_sieve` here, deliberately, and this case alone: the cached base sieve already covers
1000000 and `run_sieve` refuses to rebuild what the cache holds. The measurement pair does call it,
because there the base sieve is part of what is being timed.

The length here is 32768, which is the cap itself rather than a round number: the first batch is a
full one, so a position that ran past fifteen bits would be caught here. It passed at 1024 first.

Throwaway. -/

namespace PrimeCert.SegTune.ZZC_WideOneSmoke

run_segment_variant 86 100000000000001 65536 50000 32768 1000000

end PrimeCert.SegTune.ZZC_WideOneSmoke
