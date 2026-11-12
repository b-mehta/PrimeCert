/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The window marked by keeping rather than removing

Mode 18 builds each divisor's hits, ands them into the window, compares and subtracts. Mode 76
builds the complement of those hits instead, which costs the same because it repeats with the same
period and tiles by the same doubling, and then marks with one `land` and nothing else. So the
saving is the compare, the subtraction pass and one copy of the window a divisor, with the mask
construction untouched.

Pair with `ZG_Doubling`, which is mode 18 over the same divisors. The emitter refuses to emit
unless keeping leaves exactly the window removing leaves.

**Measured 2026-11-12, and it loses. Do not rebuild it.** Fresh c7i.8xlarge, `run.sh 3`, load
about 1: kernel 96.9-97.3 s against Doubling's 95.5-96.3 (+1.5%), processor 181-182 against
136.8-138.3 (+32%), and the whole processor gap is in the elaborator, 180 s of window against 136.
So the compare and the subtraction that keeping removes are not what the kernel is spending its
time on, and building the complement costs the emitter a third of the run. -/

namespace PrimeCert.SegTune.ZZR_Keep

run_sieve 10000000

run_segment_variant 76 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZZR_Keep
