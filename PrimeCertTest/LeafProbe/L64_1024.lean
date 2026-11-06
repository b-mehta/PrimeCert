/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.QuickRfl
public import PrimeCert.PrimeHarmonic

/-! # 2 special leaves at 1024 positions, first 64 primes removed

A special leaf of the paper's identity is the sum of 1/i over a prefix of an
interval whose least prime factor exceeds the b-th prime, so sieving the interval
by the first b primes and folding over the survivors is exactly that leaf. The
identity needs 1.16e7 of them at x = 1e14, against 21600 seconds in a runner, so
the cost of one decides whether that route fits.

Sibling files hold the other values of b and of the prefix length. Nothing here is
proved to be a leaf of anything; the file is for timing.
-/

set_option linter.style.longLine false

namespace PrimeCert.LeafProbe.L64_1024

open PrimeCert

/-- 290 survivors of 1024 positions from 333507414. -/
public theorem leaf_0 : Nat.beq (sumB (recipAtW 42485278824602871247001464978807761382054353959682588826758514440145990916261397401324406191193218376808924942017116086219152639052088134488856815626088167020421048774418941205125943972472823721231658480031317420032768395240983312290900827508876969824146088809586822102669777224899434000009983511651999037448 333507414 100000000000000000000) 0 1024 1) 28984818633817 = true := by
  quickRfl

/-- 290 survivors of 1024 positions from 333508438. -/
public theorem leaf_1 : Nat.beq (sumB (recipAtW 49354717275429232070284831021042784533047566134353877325656847124675010482085594297944613907593456284044983766245240156247471797741179833147110636370839646417232994803844331934514981024791880191215233093780895542565848552222215945677317560285365643841061870235683817993080720908355238536035882988421857282566 333508438 100000000000000000000) 0 1024 1) 28984729782595 = true := by
  quickRfl

end PrimeCert.LeafProbe.L64_1024
