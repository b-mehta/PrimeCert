/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.WideB.Part00
public import PrimeCertTest.WideB.Part01
public import PrimeCertTest.WideB.Part02
public import PrimeCertTest.WideB.Part03

/-! # The primes from `1005969665` to `1609949440`, in one enclosure

The 4 parts sum 96 segments of 2097152 wheel positions between them; this joins
all of them into one enclosure of the sum of the reciprocals of the primes above `1005969664` and
below `1609949441`.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_join 1005969665 2097152 150001 20 96
