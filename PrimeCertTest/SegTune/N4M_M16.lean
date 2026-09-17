/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The window sieve at 4194304 candidates

The ladder's anchor width, through mode 16, so that `N1M_M16` and `N2M_M16` are compared against
it on equal footing rather than against the mode 3 figure. -/

namespace PrimeCert.SegTune.N4M_M16

run_sieve 10000000

run_segment_variant 16 100000000000001 4194304 3333332 1536 10000000

end PrimeCert.SegTune.N4M_M16
