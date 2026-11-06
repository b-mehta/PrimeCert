/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.QuickRfl
public import PrimeCert.PrimeHarmonic

/-! # 2 special leaves at 1024 positions, first 4797 primes removed

A special leaf of the paper's identity is the sum of 1/i over a prefix of an
interval whose least prime factor exceeds the b-th prime, so sieving the interval
by the first b primes and folding over the survivors is exactly that leaf. The
identity needs 1.16e7 of them at x = 1e14, against 21600 seconds in a runner, so
the cost of one decides whether that route fits.

Sibling files hold the other values of b and of the prefix length. Nothing here is
proved to be a leaf of anything; the file is for timing.
-/

set_option linter.style.longLine false

namespace PrimeCert.LeafProbe.L4797_1024

open PrimeCert

/-- 146 survivors of 1024 positions from 334029654. -/
public theorem leaf_0 : Nat.beq (sumB (recipAtW 112377851564836199579647354585209859361720027645818500186389107306113353083080421387486688023999796189753974198321132435985804250242203998930669400357484702179502285171024979506031226105226868948412616845205385636797951828733391529708886057990999005973336242484292862215518770483820603894801866833151897108992 334029654 100000000000000000000) 0 1024 1) 14569540515780 = true := by
  quickRfl

/-- 159 survivors of 1024 positions from 334030678. -/
public theorem leaf_1 : Nat.beq (sumB (recipAtW 44231875472778858613794346271470935960337821635920766641123216235308124548778986800034654901753655388470274237832005202944342316586856571415012671342178277226797335684191998495382072645048327092473770863586630582433247799166074490186652926882381580218768885619376661947319613216235762448479300292561863040 334030678 100000000000000000000) 0 1024 1) 15866781404877 = true := by
  quickRfl

end PrimeCert.LeafProbe.L4797_1024
