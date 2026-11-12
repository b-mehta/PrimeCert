/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCertTest.LaneChain

/-! # The same window with one more band sorted

Mode 82 is mode 28 with the octave where a divisor's eightfold fits the window and its sixteenfold
does not sorted at sixteen records a divisor, rather than given a mask. Pair with
`ZZH_FullWindow28`, which is the same window on the route the sieve runs today.

Measured in isolation on 2026-11-12, that band alone came to kernel 22.59-22.88 s sorted against
25.95-26.25 masked (`ZZV_Lane16` against `ZZW_Lane16Mask`), so the gap to look for here is about
3.4 s of a window's 157 s of kernel, a little over 2%. That is small enough that it needs both
arms in one job to resolve: hosts vary by far more than that.

`PrimeCertTest.LaneChain` is imported because `stripeStepBand16` lives there; the emitter names
that import if it is missing.

**Measured 2026-11-12, and mode 82 loses. Do not land it.** Both arms in one job, fresh
c7i.8xlarge, `run.sh 3`, load about 1, ranges not overlapping:

|                     | mode 28         | mode 82         |
| kernel total        | 161.2-163.3 s   | 166.6-168.1 s   |
| batch lemmas        | 44.3-44.6       | 25.1-25.2       |
| sorted batch lemmas | 49.3-49.5       | 72.3-73.5       |
| processor           | 177.7-179.7 s   | 184.0-185.6 s   |
| peak                | 2.60 GB         | 2.70 GB         |

About **3% more kernel, 3.4% more processor, 4% more peak**. The masked band does fall by 19.3 s,
exactly as intended, but the sorted band rises by 23.5 s, so sorting that octave costs more than
the masks it replaces.

**Why the isolated pair said otherwise.** `ZZV_Lane16` against `ZZW_Lane16Mask` ran both arms at
batch length 4096, where sorting won by 13% of that band. Production reaches that band through the
graded schedule, at 256 to 768. The isolated verdict was real at 4096 and did not transfer, which
is the same trap as the void batch-length lead of 2026-11-11: **measure in the shape a run uses, or
the number does not carry.** -/

namespace PrimeCert.SegTune.ZZJ_FullWindow82

run_sieve 10000000

run_segment_variant 82 100000000000001 4194304 3333333 8192 10000000

end PrimeCert.SegTune.ZZJ_FullWindow82
