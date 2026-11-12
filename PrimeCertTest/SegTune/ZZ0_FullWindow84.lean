/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same window with the smallest divisors in longer batches

Mode 84 is mode 28 with `batchLenLow` in place of `batchLen`: the bottom tier at **1024** where the
default gives 256, below base index 20000, and the other three tiers untouched. No proof is
involved.

**This is the last of the schedule's four tiers to be varied on its own.** `batchLenWide` moved the
top tier (mode 83) and `batchLenMid` the two middle ones (mode 57), both measured on 2026-11-12 and
both decided against. The sweep of 2026-11-11 that settled batch length moved every tier together
as uniform lengths, so it never isolated this one. Those smallest divisors carry the densest masks
in the run and sit in the masked band, about 44 s of a window's 150.

Pair with `ZZH_FullWindow28`, both arms in one job, and report peak for each. The two tiers already
measured went opposite ways — longer middle batches bought time and cost memory, shorter wide ones
cost time and saved it — so this needs reading on windows per machine-hour rather than seconds, and
the packing has to come from a measured marginal rather than the per-process peak. -/

namespace PrimeCert.SegTune.ZZ0_FullWindow84

run_sieve 10000000

run_segment_variant 84 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZ0_FullWindow84
