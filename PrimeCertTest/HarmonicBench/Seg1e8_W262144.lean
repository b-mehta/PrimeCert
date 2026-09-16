/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A window of 262144 positions just above `10 ^ 8`, about 786 thousand numbers -/

namespace PrimeCert.Seg1e8W18

run_segment 100000001 262144 10542 1536

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_segment 100000001 262144 31627 20 2048 1536

end PrimeCert.Seg1e8W18
