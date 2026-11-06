/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # One segment of 4194304 positions, the width the record ran at

Paired with `Seg1M`, which differs only in the segment width.
-/

namespace PrimeCert.OleanSize.Seg4M

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1005969665 4194304 150001 20 2048 1536 1 15

end PrimeCert.OleanSize.Seg4M
