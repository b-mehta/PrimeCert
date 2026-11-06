/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.QuickRfl
public import PrimeCert.PrimeHarmonic

/-! # 2 special leaves at 1024 positions, first 16 primes removed

A special leaf of the paper's identity is the sum of 1/i over a prefix of an
interval whose least prime factor exceeds the b-th prime, so sieving the interval
by the first b primes and folding over the survivors is exactly that leaf. The
identity needs 1.16e7 of them at x = 1e14, against 21600 seconds in a runner, so
the cost of one decides whether that route fits.

Sibling files hold the other values of b and of the prefix length. Nothing here is
proved to be a leaf of anything; the file is for timing.
-/

set_option linter.style.longLine false

namespace PrimeCert.LeafProbe.L16_1024

open PrimeCert

/-- 411 survivors of 1024 positions from 333333334. -/
public theorem leaf_0 : Nat.beq (sumB (recipAtW 110606588886201614721011271535036629675931289746820969413565795936102358856298416187610872526215412758468808401416906481958779331045325153785129042502994131653687800918600823833889039030208137838996025441076036910931596282554663440329088073162477751000306276607614247160261804004197073634544153033307398934126 333333334 100000000000000000000) 0 1024 1) 41099936576900 = true := by
  quickRfl

/-- 426 survivors of 1024 positions from 333334358. -/
public theorem leaf_1 : Nat.beq (sumB (recipAtW 4947972771078396260653840078498246403515794920802488239113119038987201897456907394540301656421441232075300818395021491291474704575022328197497853581547127260351579871806814827779294429779522140553261654278463082803656996785271373126957463049783392699530916755695512831570309256497562975993036350259012178144 333334358 100000000000000000000) 0 1024 1) 42599802962948 = true := by
  quickRfl

end PrimeCert.LeafProbe.L16_1024
