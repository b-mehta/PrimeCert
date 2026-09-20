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
public import PrimeCertTest.Higher.Part12
public import PrimeCertTest.Higher.Part13
public import PrimeCertTest.Higher.Part14
public import PrimeCertTest.Higher.Part15
public import PrimeCertTest.Higher.Part16
public import PrimeCertTest.Higher.Part17
public import PrimeCertTest.Higher.Part18
public import PrimeCertTest.Higher.Part19
public import PrimeCertTest.Higher.Part20
public import PrimeCertTest.Higher.Part21
public import PrimeCertTest.Higher.Part22
public import PrimeCertTest.Higher.Part23
public import PrimeCertTest.Higher.Part24
public import PrimeCertTest.Higher.Part25
public import PrimeCertTest.Higher.Part26
public import PrimeCertTest.Higher.Part27
public import PrimeCertTest.Higher.Part28
public import PrimeCertTest.Higher.Part29
public import PrimeCertTest.Higher.Part30
public import PrimeCertTest.Higher.Part31
public import PrimeCertTest.Higher.Part32

/-! # The primes from `1005969665` to `10971635968`, in one enclosure

The 33 parts each sum 96 segments of 1048576 wheel positions; this joins all
3168 of them into one enclosure of the sum of the reciprocals of the primes above
`1005969664` and below `10971635969`. Adding it to the enclosure `Billion.All` gives the range from
`10 ^ 8` up, and adding the base sieve on top of that gives the sum past `10971635968`.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_join 1005969665 1048576 110017 20 3168
