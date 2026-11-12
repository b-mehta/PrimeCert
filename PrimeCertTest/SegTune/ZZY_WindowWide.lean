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

The reasoning for why the answer is not obvious is in `ZZX_WindowNarrow`. -/

namespace PrimeCert.SegTune.ZZY_WindowWide

run_sieve 10000000

run_segment 100000000000001 8388608 333333 8192 10000000

end PrimeCert.SegTune.ZZY_WindowWide
