/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The same range in 12 segments of 2097152 positions (see `MemW1048`) -/

namespace PrimeCert.MemW2097

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 2097152 110017 20 2048 1536 12 15

end PrimeCert.MemW2097
