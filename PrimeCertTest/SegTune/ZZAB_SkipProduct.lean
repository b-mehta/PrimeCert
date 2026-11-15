/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The skipped product said rather than asserted

`parts 67`, which is `ZZAA_RecordAssemble`'s 51 plus 64: the same arm again, with the skipped
product established from its own records instead of handed to the kernel as a literal nobody
checked. That literal is the last asserted one in the chain.

The shape is the live side's, over the skipped divisors: a chunk of records at a time with its
product and its assembly, then the chunk products combined pairwise by multiplications the kernel
checks, ending at the literal the gcds are stated against. The emitter refuses to emit if the
chunks multiply to anything else.

The open question is the top of that tree. Near the leaves the operands are a few kilobytes; near
the root they are most of a megabyte each, and what the kernel does with a multiplication that
size is not something earlier arms have measured. The pairwise shape was chosen because the
emitter's own sequential build cost 57.2 s, but that was the emitter, not the kernel, and the two
are separate questions.

Pair with `ZZAA_RecordAssemble`, one job, alternating, peak each. The difference is the whole cost
of saying the skipped product rather than asserting it.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAB_SkipProduct

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 67 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAB_SkipProduct
