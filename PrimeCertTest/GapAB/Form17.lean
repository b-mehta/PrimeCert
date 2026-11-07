/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Form 15's segment with one declaration a batch removed

Form 15 names each batch's fold equation and then uses that name once, in the equation against
the segment literal. Form 17 is the same run with the first of those inlined into the second, so
a batch costs two declarations rather than three and the kernel checks the same thing. The
measurements that closed the walk said a declaration is worth about four points, which is what
this tests on the path a record actually uses.
-/

namespace PrimeCert.GapAB.Form17

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 65536 100003 20 2048 1536 1 17

end PrimeCert.GapAB.Form17
