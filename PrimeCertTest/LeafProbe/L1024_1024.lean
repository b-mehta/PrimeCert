/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.QuickRfl
public import PrimeCert.PrimeHarmonic

/-! # 2 special leaves at 1024 positions, first 1024 primes removed

A special leaf of the paper's identity is the sum of 1/i over a prefix of an
interval whose least prime factor exceeds the b-th prime, so sieving the interval
by the first b primes and folding over the survivors is exactly that leaf. The
identity needs 1.16e7 of them at x = 1e14, against 21600 seconds in a runner, so
the cost of one decides whether that route fits.

Sibling files hold the other values of b and of the prefix length. Nothing here is
proved to be a leaf of anything; the file is for timing.
-/

set_option linter.style.longLine false

namespace PrimeCert.LeafProbe.L1024_1024

open PrimeCert

/-- 190 survivors of 1024 positions from 333855574. -/
public theorem leaf_0 : Nat.beq (sumB (recipAtW 11590236159267988579836684435452849638947960678157915299798992143452063076476826363333310201136941205148962548656889539472623387306543058658366141210554823669986727996228004278660208824312012438773008855206541735353436611690607714585884594510743895411986279304598415649181348945789077623197433693465418727424 333855574 100000000000000000000) 0 1024 1) 18970249568364 = true := by
  quickRfl

/-- 194 survivors of 1024 positions from 333856598. -/
public theorem leaf_1 : Nat.beq (sumB (recipAtW 877994327348390507536407565598306462667932316919485402410983291539819331787415643535940463823329510254225771096025494853106762263449731969184040979299380285870240242948510970498081084794017361028422908870288940820166697477250837772025152755785600538048411477072236996782473114871464385917564028977789731392 333856598 100000000000000000000) 0 1024 1) 19369561974524 = true := by
  quickRfl

end PrimeCert.LeafProbe.L1024_1024
