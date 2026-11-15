/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The record certificate with the records tied to the window

`parts 51`, which is `ZZZ_RecordFull`'s 19 plus 32: the same arm, and beside each chunk's gcd the
statement that the chunk's records assemble to the bits the emitter says they do.

The gcds alone say that some 256 numbers share no factor with the skipped product. They do not say
those numbers are the window's live positions, so on their own they certify nothing about the
window. `asmChunkK` is the half that does, and this arm is what says whether the kernel can afford
it: 256 slots a chunk, each a shift of `1` by a 16-bit position, folded with `lor` at depth 8.

What the chunks assemble to is still asserted a chunk at a time rather than combined into the
slice, so this is a cost question and not yet a proof. Combining them is literal-to-literal work
and cheap to add once the reduction here is known to be affordable.

Pair with `ZZZ_RecordFull`, one job, alternating, peak each. The difference between the two is the
whole cost of the assembly statements.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAA_RecordAssemble

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 51 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAA_RecordAssemble
