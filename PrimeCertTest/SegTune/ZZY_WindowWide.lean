/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The window at twice the width the sieve runs today

A plain `run_segment` at 8388608 bits, covering 25165824 integers, against `ZZX_WindowNarrow` at
half that. Read the two as kernel seconds per integer covered, and read their peaks as well: this
arm holds a window twice the size, so it may win on processor seconds and still lose a run the
packing a smaller peak allows.

The reasoning for why the answer is not obvious is in `ZZX_WindowNarrow`.

**Measured 2026-11-12, and the width should stay where it is.** Fresh c7i.8xlarge, `run.sh 3`,
load about 1. Narrow: kernel 104.7-106.1 s, processor 152.2-155.2 s, peak 11.76 GB. Wide: kernel
201.7-205.2 s, processor 324-330 s, peak 22.47 GB. Per integer covered that is 3% less kernel, 7%
more processor, and 1.9 times the peak. Since a run packs windows onto a machine and the peak sets
how many fit, 3% of kernel does not buy back half the packing. The width is now measured rather
than assumed, which it had never been. -/

namespace PrimeCert.SegTune.ZZY_WindowWide

run_sieve 10000000

run_segment 100000000000001 8388608 333333 8192 10000000

end PrimeCert.SegTune.ZZY_WindowWide
