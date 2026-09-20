/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Eight segments sieved and summed, against `Split8_Sieve` which only sieves

The record summed about 8.3e8 primes in 38755 runner seconds, so 46.7 microseconds a prime, where
the emitted work for a prime is one division and one addition. This pair says how much of that
belongs to the summing and how much to crossing off, at the shape the record actually ran: the
same start, width, fuel and batch length in both, form 15 here and no summing at all there.
-/

namespace PrimeCert.Split8_Full

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 8 15

end PrimeCert.Split8_Full
