/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.Higher2.Part00
public import PrimeCertTest.Higher2.Part01
public import PrimeCertTest.Higher2.Part02
public import PrimeCertTest.Higher2.Part03
public import PrimeCertTest.Higher2.Part04
public import PrimeCertTest.Higher2.Part05
public import PrimeCertTest.Higher2.Part06
public import PrimeCertTest.Higher2.Part07
public import PrimeCertTest.Higher2.Part08
public import PrimeCertTest.Higher2.Part09
public import PrimeCertTest.Higher2.Part10
public import PrimeCertTest.Higher2.Part11
public import PrimeCertTest.Higher2.Part12
public import PrimeCertTest.Higher2.Part13
public import PrimeCertTest.Higher2.Part14
public import PrimeCertTest.Higher2.Part15
public import PrimeCertTest.Higher2.Part16
public import PrimeCertTest.Higher2.Part17
public import PrimeCertTest.Higher2.Part18
public import PrimeCertTest.Higher2.Part19
public import PrimeCertTest.Higher2.Part20
public import PrimeCertTest.Higher2.Part21
public import PrimeCertTest.Higher2.Part22
public import PrimeCertTest.Higher2.Part23
public import PrimeCertTest.Higher2.Part24
public import PrimeCertTest.Higher2.Part25

/-! # The primes from `5586149633` to `10166329600`, in one enclosure

The 26 parts each sum 56 segments of 1048576 wheel positions; this joins all
1456 of them into one enclosure of the sum of the reciprocals of the primes above
`5586149632` and below `10166329601`.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_join 5586149633 1048576 110017 20 1456
