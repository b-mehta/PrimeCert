/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.Phi
public meta import PrimeCert.SegmentedSieve

/-!
# One sweep, every bound

A sieved leaf wants the sum at its own bound, and the bounds of an expansion are every prime
below the cut. Sieving separately for each costs many times a single sweep, so the sweep is
shared: `segRun_rung` carries the run at one bound on to the next, and the kernel pays only the
steps between them.

`run_segment_ladder a W fuel len y` emits one rung per prime from the base run's bound up to `y`,
each stating `Sieve.segRun s a W p = lit` for that bound's literal. The base rung is the equation
`run_segment_variant` already emits, so the ladder starts from tested ground.
-/

namespace PrimeCert.PhiLadder

open Lean Elab Command Meta

/-- The `k`-th integer coprime to 6, as the wheel numbers them. -/
meta def wheelValue (k : Nat) : Nat := (k * 3 + 1) + k % 2

/-- Its inverse on the integers coprime to 6. -/
meta def wheelIndex (q : Nat) : Nat := (q - 1) / 3

/-- `lhs = rhs` at `Nat`. -/
meta def mkNatEq (lhs rhs : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Nat) lhs rhs

/-- Add `name : type := value` as a theorem. -/
meta def addRungThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- The primes in `lo+1 … hi`, in rising order. -/
meta def primesBetween (lo hi : Nat) : Array Nat := Id.run do
  if hi < 2 then return #[]
  let mut flags := Array.replicate (hi + 1) true
  flags := flags.set! 0 false
  flags := flags.set! 1 false
  let mut p := 2
  while p * p ≤ hi do
    if flags[p]! then
      let mut m := p * p
      while m ≤ hi do
        flags := flags.set! m false
        m := m + p
    p := p + 1
  let mut out : Array Nat := #[]
  for i in [lo + 1:hi + 1] do
    if flags[i]! then out := out.push i
  return out

/-- Emit a rung for every prime from the base run's bound up to `y`. -/
meta def runSegmentLadder (a W fuel len y mode : Nat) : MetaM Unit := do
  let ns ← getCurrNamespace
  let env ← getEnv
  let tag := if mode ≥ 16 then s!"{a}_{W}_{fuel}_{Nat.max 1 len}_m{mode}"
    else s!"{a}_{W}_{fuel}_{Nat.max 1 len}"
  let segLit := ns ++ Name.mkSimple (if mode ≥ 16 then s!"segBitsV_{tag}" else s!"segBits_{tag}")
  let segEqI := ns ++ Name.mkSimple s!"segEqI_{tag}"
  let some info := env.find? segLit
    | throwError "run_segment_ladder: no segment {segLit}; run \
`run_segment_variant {mode} {a} {W} {fuel} {len}` above this command"
  let some lit0 := info.value?.bind Expr.rawNatLit?
    | throwError "run_segment_ladder: the segment {segLit} is not a numeral"
  let some baseInfo := env.find? segEqI
    | throwError "run_segment_ladder: no equation {segEqI}"
  let _ := baseInfo
  let some cache ← Sieve.findSieveCache y
    | throwError "run_segment_ladder: no sieve cache in scope covers {y}"
  let some sInfo := env.find? cache.litName
    | throwError "run_segment_ladder: no base sieve {cache.litName}"
  let some sVal := sInfo.value?.bind Expr.rawNatLit?
    | throwError "run_segment_ladder: the base sieve is not a numeral"
  let lo := Sieve.index a
  let wm1 := W - 1
  let sE := mkConst cache.litName
  let aE := mkRawNatLit a
  let WE := mkRawNatLit W
  let base := wheelValue fuel
  let mut prevB := base
  let mut prevIdx := fuel
  let mut prevLit := lit0
  let mut prevName := segEqI
  let mut rungs := 0
  for p in primesBetween base y do
    let idx := wheelIndex p
    if wheelValue idx != p then
      continue
    let d := idx - prevIdx
    let lit := Sieve.segLoop sVal lo wm1 prevLit (1 + prevIdx) d
    let name := ns ++ Name.mkSimple s!"segLadder_{a}_{W}_{len}_{p}"
    addRungThm name
      (mkNatEq (mkAppN (mkConst ``Sieve.segRun) #[sE, aE, WE, mkRawNatLit p]) (mkRawNatLit lit))
      (mkAppN (mkConst ``segRun_rung)
        #[sE, aE, WE, mkRawNatLit prevB, mkRawNatLit p, mkRawNatLit d, mkRawNatLit prevLit,
          mkRawNatLit lit, Lean.reflBoolTrue, mkConst prevName, Lean.reflBoolTrue])
    prevB := p
    prevIdx := idx
    prevLit := lit
    prevName := name
    rungs := rungs + 1
  logInfo s!"run_segment_ladder: {rungs} rungs from {base} to {prevB}, \
window of {W} positions from {a}"

/-- `run_segment_ladder a W fuel len y mode` emits one rung per prime up to `y` (see
`runSegmentLadder`). -/
elab "run_segment_ladder" aStx:num wStx:num fStx:num lStx:num yStx:num mStx:num : command =>
  liftTermElabM <|
    runSegmentLadder aStx.getNat wStx.getNat fStx.getNat lStx.getNat yStx.getNat mStx.getNat

end PrimeCert.PhiLadder
