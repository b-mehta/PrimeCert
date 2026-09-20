/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Sorting every batch and then throwing the records away

The sorted shape costs about seventy seconds more to elaborate than the shape it replaces, and that
handback is what stops a segment's halved kernel time reaching the runner. Two things could be
paying it: the sort itself, which runs in the metaprogram, and the records the sorted batches emit
that the plain ones do not. This file runs the sort and then settles every batch the plain way, so
against `S7_Sched` it is the sort alone and against `S9_Stripes` it is the records alone. Its
emitted statements are `S7_Sched`'s. -/

namespace PrimeCert.SegTune.G7_SortOnly

run_sieve 10000000

run_segment_variant 39 100000000000001 4194304 3333332 8192 10000000

end PrimeCert.SegTune.G7_SortOnly
