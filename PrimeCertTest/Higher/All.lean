/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public import PrimeCertTest.Higher.Part00
public import PrimeCertTest.Higher.Part01
public import PrimeCertTest.Higher.Part02
public import PrimeCertTest.Higher.Part03
public import PrimeCertTest.Higher.Part04
public import PrimeCertTest.Higher.Part05
public import PrimeCertTest.Higher.Part06
public import PrimeCertTest.Higher.Part07
public import PrimeCertTest.Higher.Part08
public import PrimeCertTest.Higher.Part09
public import PrimeCertTest.Higher.Part10
public import PrimeCertTest.Higher.Part11

/-! # The primes from `1005969665` to `2817908992`, in one enclosure

The twelve parts each sum 192 windows of 262144 wheel positions; this joins all 2304 of them into
one enclosure of the sum of the reciprocals of the primes above `1005969664` and below `2817908993`.
Adding it to the enclosure `Billion.All` gives the range from `10 ^ 8` up, and adding the base sieve
on top of that gives the sum past `2.8 * 10 ^ 9`.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_join 1005969665 262144 53087 20 2304
