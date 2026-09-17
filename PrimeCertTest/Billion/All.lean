/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.Billion.Part00
public import PrimeCertTest.Billion.Part01
public import PrimeCertTest.Billion.Part02
public import PrimeCertTest.Billion.Part03
public import PrimeCertTest.Billion.Part04
public import PrimeCertTest.Billion.Part05
public import PrimeCertTest.Billion.Part06
public import PrimeCertTest.Billion.Part07
public import PrimeCertTest.Billion.Part08
public import PrimeCertTest.Billion.Part09
public import PrimeCertTest.Billion.Part10
public import PrimeCertTest.Billion.Part11

/-! # The primes from `100000001` to `1005969664`, in one enclosure

The twelve parts each sum 96 windows of 262144 wheel positions; this joins all 1152 of them into one
enclosure of the sum of the reciprocals of the primes above `10 ^ 8` and below `1005969665`. Adding
it to the enclosure for the primes up to `10 ^ 8` gives the sum past a billion.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_join 100000001 262144 31721 20 1152
