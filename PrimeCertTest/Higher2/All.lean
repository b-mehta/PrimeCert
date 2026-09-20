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
public import PrimeCertTest.Higher2.Part26
public import PrimeCertTest.Higher2.Part27
public import PrimeCertTest.Higher2.Part28
public import PrimeCertTest.Higher2.Part29
public import PrimeCertTest.Higher2.Part30
public import PrimeCertTest.Higher2.Part31
public import PrimeCertTest.Higher2.Part32
public import PrimeCertTest.Higher2.Part33
public import PrimeCertTest.Higher2.Part34
public import PrimeCertTest.Higher2.Part35
public import PrimeCertTest.Higher2.Part36
public import PrimeCertTest.Higher2.Part37
public import PrimeCertTest.Higher2.Part38
public import PrimeCertTest.Higher2.Part39
public import PrimeCertTest.Higher2.Part40
public import PrimeCertTest.Higher2.Part41
public import PrimeCertTest.Higher2.Part42
public import PrimeCertTest.Higher2.Part43
public import PrimeCertTest.Higher2.Part44
public import PrimeCertTest.Higher2.Part45
public import PrimeCertTest.Higher2.Part46
public import PrimeCertTest.Higher2.Part47
public import PrimeCertTest.Higher2.Part48
public import PrimeCertTest.Higher2.Part49
public import PrimeCertTest.Higher2.Part50
public import PrimeCertTest.Higher2.Part51
public import PrimeCertTest.Higher2.Part52
public import PrimeCertTest.Higher2.Part53
public import PrimeCertTest.Higher2.Part54
public import PrimeCertTest.Higher2.Part55
public import PrimeCertTest.Higher2.Part56
public import PrimeCertTest.Higher2.Part57
public import PrimeCertTest.Higher2.Part58
public import PrimeCertTest.Higher2.Part59
public import PrimeCertTest.Higher2.Part60
public import PrimeCertTest.Higher2.Part61
public import PrimeCertTest.Higher2.Part62
public import PrimeCertTest.Higher2.Part63
public import PrimeCertTest.Higher2.Part64

/-! # The primes from `10820641025` to `20635312384`, in one enclosure

The 65 parts each sum 12 segments of 4194304 wheel positions; this joins all
780 of them into one enclosure of the sum of the reciprocals of the primes above
`10820641024` and below `20635312385`.
-/

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_join 10820641025 4194304 150001 20 780
