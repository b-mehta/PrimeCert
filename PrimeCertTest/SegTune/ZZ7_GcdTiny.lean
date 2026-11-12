/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A tiny mode 75, to check the runner reports its three timers

`ZZQ_GcdPrice` at a size that fits a small box. It measures nothing worth reading; it exists so
that `run.sh`'s gcd rows can be checked against a real run before a real one is asked for.
Throwaway. -/

namespace PrimeCert.SegTune.ZZ7_GcdTiny

run_segment_variant 75 100000000000001 131072 2000 2048 1000000

end PrimeCert.SegTune.ZZ7_GcdTiny
