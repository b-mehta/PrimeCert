/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PhiExpand

/-! # A whole expansion, emitted

`phiB 1000 7`, the numbers up to 1000 with no prime factor at or below 7, reached by the
recurrence rather than by sieving: a branch at each of 2, 3, 5 and 7, a step past each composite
bound between them, and the harmonic fold at the bottom of every branch.
-/

namespace PrimeCert.PhiExpandTest

set_option maxRecDepth 100000 in
run_phi_expand 1000 7 20

/-! The same height at higher bounds, to show how the node count grows while the expansion runs
to the bottom with no cut. -/

set_option maxRecDepth 100000 in
run_phi_expand 1000 13 20

set_option maxRecDepth 100000 in
run_phi_expand 1000 23 20

/-! With a cut, a branch whose height falls below it stops and waits for a leaf from the sieve
side. Nothing supplies those here, so the command reports the demand rather than closing. -/

set_option maxRecDepth 100000 in
run_phi_expand 1000 23 20 100

end PrimeCert.PhiExpandTest
