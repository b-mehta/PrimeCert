/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve
public import PrimeCertTest.HarmonicBench.SieveHt12

/-! # One window at `10 ^ 12` in the paper's own variables

The count of the primes, the total of their offsets from the first number of the window, and the
total of the squares of those offsets. The enclosure is the one `TaylorHt12` proves; the numbers
the kernel adds up are smaller.
-/

namespace PrimeCert.TaylorOHt12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000000001 262144 1000001 20 2048 1536 1 10

end PrimeCert.TaylorOHt12
