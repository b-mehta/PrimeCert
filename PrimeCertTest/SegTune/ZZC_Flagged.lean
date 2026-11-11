/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The shorter length with the out-of-window records dropped

Third of the three arms described in `ZZA_Len8192`, and the one under test. Mode 72 emits only
the records whose strike lands inside the window and flags the last of each progression, which
then accounts for the strikes after it. The kernel honours the flag only when the next strike is
really past the end, so flagging early makes the batch's tally come up short and the check fail.

Unlike the screen that measured the ceiling, this keeps the tally complete, so it is a candidate
rather than a bound. Read it against `ZZB_Len4096`, not against `ZZA_Len8192`. -/

namespace PrimeCert.SegTune.ZZC_Flagged

run_sieve 10000000

run_segment_variant 72 100000000000001 4194304 333333 4096 10000000

end PrimeCert.SegTune.ZZC_Flagged
