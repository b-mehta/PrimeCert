/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PhiExpand
public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # The expansion closing on leaves produced for it

`run_phi_expand 1000 23 20 100` stops every branch whose height falls below 100 and takes its
value from a leaf. The leaves are produced here first, each from the two base runs its height and
bound need, so the expansion finds them and reaches a root.

Without the cut the same value takes 203 nodes. The point of the cut is that the nodes it saves
are the ones a real target has too many of.
-/

namespace PrimeCert.PhiCutTest

run_harmonic 23 20 256

run_harmonic 90 20 256
run_harmonic 10 20 256
run_phi_leaf 90 10 20 256

run_harmonic 76 20 256
run_harmonic 12 20 256
run_phi_leaf 76 12 20 256

run_harmonic 58 20 256
run_harmonic 16 20 256
run_phi_leaf 58 16 20 256

run_harmonic 52 20 256
run_harmonic 18 20 256
run_phi_leaf 52 18 20 256

run_harmonic 43 20 256
run_harmonic 22 20 256
run_phi_leaf 43 22 20 256

set_option maxRecDepth 100000 in
run_phi_expand 1000 23 20 100

end PrimeCert.PhiCutTest
