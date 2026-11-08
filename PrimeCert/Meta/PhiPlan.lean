/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.Phi

/-!
# Counting the leaves of the expansion, inside the emitter

`phiB t B` expands into one term per prime above `B`, each term the same function at `t / p` and a
lower bound. Walking that fully is too large, so a branch stops when the squarefree product `m` it
has accumulated passes the cut `y`, and otherwise when it reaches the bottom. The first kind is
answered by sieving at the branch's height, the second by the plain harmonic sum.

`run_phi_plan x` reports how many of each kind the cut `y = x ^ (1/3)` gives, which is what the
emitter has to produce. `scripts/count_leaves.py` computes the same numbers independently.
-/

namespace PrimeCert.PhiPlan

open Lean Elab Command Meta

/-- The primes at most `n`, by sieving. -/
meta def primesUpTo (n : Nat) : Array Nat := Id.run do
  if n < 2 then return #[]
  let mut flags := Array.replicate (n + 1) true
  flags := flags.set! 0 false
  flags := flags.set! 1 false
  let mut p := 2
  while p * p ≤ n do
    if flags[p]! then
      let mut m := p * p
      while m ≤ n do
        flags := flags.set! m false
        m := m + p
    p := p + 1
  let mut out : Array Nat := #[]
  for i in [0:n + 1] do
    if flags[i]! then out := out.push i
  return out

/-- The largest `r` with `r ^ 3 ≤ n`. -/
meta def cubeRoot (n : Nat) : Nat := Id.run do
  let mut r := 0
  while (r + 1) * (r + 1) * (r + 1) ≤ n do
    r := r + 1
  return r

/-- The leaves of the expansion cut at `y`, counted rather than stored. A branch carries the
squarefree product `m` of the primes it has been cut by, and may be cut again only by primes below
the one that made it. It ends as a special leaf when the product passes `y`, and contributes an
ordinary leaf whenever the product is still at most `y`. -/
meta partial def leafCounts (y : Nat) (primes : Array Nat) : Nat × Nat × Nat := Id.run do
  let mut ordinary := 0
  let mut special := 0
  let mut maxDivisor := 1
  let mut stack : Array (Nat × Nat) := #[(1, primes.size)]
  while stack.size > 0 do
    let (m, hi) := stack.back!
    stack := stack.pop
    if m ≤ y then
      ordinary := ordinary + 1
      if m > maxDivisor then maxDivisor := m
    for b in [0:hi] do
      let mp := m * primes[b]!
      if mp > y then special := special + 1
      else stack := stack.push (mp, b)
  return (ordinary, special, maxDivisor)

/-- Report the leaf counts at the cut `y = x ^ (1/3)`. -/
meta def runPhiPlan (x : Nat) : MetaM Unit := do
  if x < 8 then
    throwError "run_phi_plan: {x} is too small to cut"
  let y := cubeRoot x
  let primes := primesUpTo y
  let (ordinary, special, maxDivisor) := leafCounts y primes
  logInfo s!"run_phi_plan: x = {x}, y = {y}, a = {primes.size}; \
ordinary leaves {ordinary}, special leaves {special}, sieve to {x / y}. \
Ordinary heights run from {x / maxDivisor} up to {x}, the top one being the branch cut by nothing"

/-- `run_phi_plan x` reports the leaves of the expansion of `x` cut at its cube root. -/
elab "run_phi_plan" xStx:num : command =>
  liftTermElabM <| runPhiPlan xStx.getNat

end PrimeCert.PhiPlan
