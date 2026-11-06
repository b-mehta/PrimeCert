/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.QuickRfl
public import PrimeCert.PrimeHarmonic

/-! # 2 special leaves at 1024 positions, first 256 primes removed

A special leaf of the paper's identity is the sum of 1/i over a prefix of an
interval whose least prime factor exceeds the b-th prime, so sieving the interval
by the first b primes and folding over the survivors is exactly that leaf. The
identity needs 1.16e7 of them at x = 1e14, against 21600 seconds in a runner, so
the cost of one decides whether that route fits.

Sibling files hold the other values of b and of the prefix length. Nothing here is
proved to be a leaf of anything; the file is for timing.
-/

set_option linter.style.longLine false

namespace PrimeCert.LeafProbe.L256_1024

open PrimeCert

/-- 230 survivors of 1024 positions from 333681494. -/
public theorem leaf_0 : Nat.beq (sumB (recipAtW 353855065939088544589133727756453504768240364463574316902206536403866161326175359737645493603066579198534045006337496118897681425286985571218689157702716104335440197521833353208623390588444057498644267606497950959103735494705665750122811456437495495041795494292822283102011287102870344196524389910354866688 333681494 100000000000000000000) 0 1024 1) 22975966715760 = true := by
  quickRfl

/-- 232 survivors of 1024 positions from 333682518. -/
public theorem leaf_1 : Nat.beq (sumB (recipAtW 23878360890170936395890409766262482782651226829216161677642843172189258397627169748148990703796257613869297512021321026347011608023867770293558993145471007567296849731022253898827089871855917023042987915115956302676165599403135476933399284624728509080220665095647342453943424788571561782270001516862773664480 333682518 100000000000000000000) 0 1024 1) 23175686313064 = true := by
  quickRfl

end PrimeCert.LeafProbe.L256_1024
