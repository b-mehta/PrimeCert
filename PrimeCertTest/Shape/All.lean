/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCertTest.Shape.Part00
public import PrimeCertTest.Shape.Part01
public import PrimeCertTest.Shape.Part02
public import PrimeCertTest.Shape.Part03
public import PrimeCertTest.Shape.Part04
public import PrimeCertTest.Shape.Part05
public import PrimeCertTest.Shape.Part06
public import PrimeCertTest.Shape.Part07
public import PrimeCertTest.Shape.Part08
public import PrimeCertTest.Shape.Part09
public import PrimeCertTest.Shape.Part10
public import PrimeCertTest.Shape.Part11

/-! # Twenty-four windows above `10 ^ 12`, in the shape a real run has

Building this builds the twelve parts at once, the way a run over a long range does. Dividing its
wall time by 24 gives the cost of a window in that setting, which `Ht12` gives for a window timed on
its own. The two together say whether the difference between the two settings is a factor or a
fixed cost per window.
-/
