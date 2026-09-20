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
public import PrimeCertTest.Higher.Part33
public import PrimeCertTest.Higher.Part34
public import PrimeCertTest.Higher.Part35
public import PrimeCertTest.Higher.Part36
public import PrimeCertTest.Higher.Part37
public import PrimeCertTest.Higher.Part38
public import PrimeCertTest.Higher.Part39
public import PrimeCertTest.Higher.Part40
public import PrimeCertTest.Higher.Part41
public import PrimeCertTest.Higher.Part42
public import PrimeCertTest.Higher.Part43
public import PrimeCertTest.Higher.Part44
public import PrimeCertTest.Higher.Part45
public import PrimeCertTest.Higher.Part46
public import PrimeCertTest.Higher.Part47
public import PrimeCertTest.Higher.Part48
public import PrimeCertTest.Higher.Part49
public import PrimeCertTest.Higher.Part50
public import PrimeCertTest.Higher.Part51
public import PrimeCertTest.Higher.Part52
public import PrimeCertTest.Higher.Part53
public import PrimeCertTest.Higher.Part54
public import PrimeCertTest.Higher.Part55
public import PrimeCertTest.Higher.Part56
public import PrimeCertTest.Higher.Part57
public import PrimeCertTest.Higher.Part58
public import PrimeCertTest.Higher.Part59
public import PrimeCertTest.Higher.Part60
public import PrimeCertTest.Higher.Part61
public import PrimeCertTest.Higher.Part62
public import PrimeCertTest.Higher.Part63
public import PrimeCertTest.Higher.Part64

/-! # The primes from `1005969665` to `10820641024`, in one enclosure

The 65 parts each sum 12 segments of 4194304 wheel positions; this joins all
780 of them into one enclosure of the sum of the reciprocals of the primes above
`1005969664` and below `10820641025`.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_join 1005969665 4194304 150001 20 780
