/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The kernel finding the places itself, instead of being handed records

`E9_Sorted` hands the kernel a sorted list of records, one per strike, and has it place each one.
This asks whether the kernel can find the places as cheaply: it walks the batch's positions as the
unsorted path does, computes a divisor's value and stride once and derives all eight strikes from
them, and puts each into one of 64 leaves by dispatching on the six bits of the leaf number. No
records, no sort and no tally, so a batch owes one equation against the assembled mask rather than
three.

Same band and same divisors as `E9_Sorted`, so the pair is the two ways of placing a strike.

No prediction. What is untested is whether a pair-valued accumulator through `Nat.rec` costs what
the record fold costs, and nothing here has measured that. -/

namespace PrimeCert.SegTune.E5_Tree

run_sieve 10000000

run_segment_variant 41 100000000000001 4194304 3333332 3072 10000000

end PrimeCert.SegTune.E5_Tree
