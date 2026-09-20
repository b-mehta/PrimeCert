/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A segment walked by gaps in batches of 768 positions

The gap walk moved work off the kernel and onto the elaborator, which now takes 5.5 s of a
segment's 14.0. The elaborator's share is paid per declaration and a batch is one declaration, so
these four files hold the batch length at 768, 1536, 3072 and 6144 positions with everything else
fixed, and the `len` job times each with the kernel check on and off.
-/

namespace PrimeCert.Len0768

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 768 1 15

end PrimeCert.Len0768
