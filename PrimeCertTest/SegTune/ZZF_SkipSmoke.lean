/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does the skip set hold up on a small window

`run_segment_skip` on a small window, to check three things before a full one is spent on it: that
the emitter's own check passes, meaning the marked subset alone builds the same window as every
divisor does; that the gcds come out 1, which the kernel settles by checking each emitted literal;
and what the skip counts look like, which the emitter logs.

A threshold of 1024 rather than 32768, because the divisors here only reach 1000000 and a window
this narrow needs the marked prefix to stay small enough that something is left to skip.

Throwaway. -/

namespace PrimeCert.SegTune.ZZF_SkipSmoke

run_segment_skip 100000000000001 65536 50000 1024 1024 65536 1000000

end PrimeCert.SegTune.ZZF_SkipSmoke
