/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PhiExpand
public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # A leaf produced for the expansion to use

A branch cut below its height waits on `phiLeaf_{height}_{bound}`. For a leaf whose height lies
below the square of its bound, the survivors above the bound are the primes up to the height, so
the whole range is the difference of two runs of the base sieve.

Here the leaf is at height 90 and bound 10, one of the ones the cut at 100 asked for, and 91 is
below 100 so no segment is wanted.
-/

namespace PrimeCert.PhiLeafTest

run_harmonic 90 20 256

run_harmonic 10 20 256

run_phi_leaf 90 10 20 256

end PrimeCert.PhiLeafTest
