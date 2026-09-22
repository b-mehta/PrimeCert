/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same segment with the twin's marking pass kept

`E2_Rec2` takes the window after each batch from that batch's own assembled mask. This keeps the
second pass, in which the twin marks the window again to produce the same literal. Both emit the
same certificate, so the pair prices the pass. -/

namespace PrimeCert.SegTune.N1_TwoPass

run_sieve 10000000

run_segment_variant 55 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.N1_TwoPass
