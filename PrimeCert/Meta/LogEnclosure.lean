/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.LogEnclosure

/-!
# Emitting a logarithm

`run_log n d e` states and proves `LogEnclosure n d lo hi (10 ^ e)`: the logarithm of `n/d`
between two integers over that scale. The work is done here, in `MetaM`, and what reaches the
kernel is a tree of comparisons between numerals.

The argument is first divided by the power of two that brings it into `[1, 2)`, where the series
of `PrimeCert/LogEnclosure.lean` is short. That leaves one copy of `log 2` per halving, which the
same series gives once, from `artanh (1/3)`, and which is emitted alongside and reused.
-/

namespace PrimeCert.LogEmit

open Lean Elab Command Meta

/-- `n ≤ m` for two literals, by the comparison the kernel decides. -/
meta def mkLe (n m : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkRawNatLit n) (mkRawNatLit m) Lean.reflBoolTrue

/-- Add `name : type := value` as a theorem. -/
meta def addThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- `LogEnclosure n d lo hi S`, every number a literal. -/
meta def mkLogType (n d lo hi S : Nat) : Expr :=
  mkAppN (mkConst ``LogEnclosure)
    #[mkRawNatLit n, mkRawNatLit d, mkRawNatLit lo, mkRawNatLit hi, mkRawNatLit S]

/-- The split over `[m, n)`, together with a proof that it is what it is. The four shapes are the
empty range, one term, two to four terms at once, and a pair of halves. -/
meta partial def proveSplit (p q : Expr) (pf qf : Nat → Nat) (m n : Nat) :
    MetaM (Nat × Nat × Nat × Expr) := do
  let rb := Lean.reflBoolTrue
  let lit := mkRawNatLit
  if n ≤ m then
    return (0, 1, 1, mkAppN (mkConst ``binarySplit_of_le) #[p, q, lit m, lit n, rb])
  else if n == m + 1 then
    let (T, Q, P) := (pf m, qf m, pf m)
    return (T, Q, P, mkAppN (mkConst ``binarySplit_of_base)
      #[p, q, lit m, lit n, lit T, lit Q, lit P, rb, rb, rb, rb])
  else if n == m + 2 then
    let T := pf m * qf (m + 1) + pf m * pf (m + 1)
    let Q := qf m * qf (m + 1)
    let P := pf m * pf (m + 1)
    return (T, Q, P, mkAppN (mkConst ``binarySplit_of_base2)
      #[p, q, lit m, lit n, lit T, lit Q, lit P, rb, rb, rb, rb])
  else if n == m + 3 then
    let T := pf m * (qf (m + 1) * qf (m + 2))
      + pf m * (pf (m + 1) * qf (m + 2) + pf (m + 1) * pf (m + 2))
    let Q := qf m * (qf (m + 1) * qf (m + 2))
    let P := pf m * (pf (m + 1) * pf (m + 2))
    return (T, Q, P, mkAppN (mkConst ``binarySplit_of_base3)
      #[p, q, lit m, lit n, lit T, lit Q, lit P, rb, rb, rb, rb])
  else if n == m + 4 then
    let T := (pf m * qf (m + 1) + pf m * pf (m + 1)) * (qf (m + 2) * qf (m + 3))
      + pf m * pf (m + 1) * (pf (m + 2) * qf (m + 3) + pf (m + 2) * pf (m + 3))
    let Q := qf m * qf (m + 1) * (qf (m + 2) * qf (m + 3))
    let P := pf m * pf (m + 1) * (pf (m + 2) * pf (m + 3))
    return (T, Q, P, mkAppN (mkConst ``binarySplit_of_base4)
      #[p, q, lit m, lit n, lit T, lit Q, lit P, rb, rb, rb, rb])
  else
    let k := (m + n) / 2
    let (tl, ql, pl, hl) ← proveSplit p q pf qf m k
    let (tr, qr, pr, hr) ← proveSplit p q pf qf k n
    let T := tl * qr + pl * tr
    let Q := ql * qr
    let P := pl * pr
    return (T, Q, P, mkAppN (mkConst ``binarySplit_rec)
      #[p, q, lit m, lit n, lit k, lit tl, lit ql, lit pl, lit tr, lit qr, lit pr,
        lit T, lit Q, lit P, rb, rb, rb, rb, rb, hl, hr])

/-- The series at `u/v`, to the length its own remainder asks for: `LogEnclosure (v+u) (v-u) lo hi
S` with the two ends as tight as the split allows. -/
meta def proveSeries (u v S : Nat) : MetaM (Nat × Nat × Expr) := do
  if u == 0 then
    throwError "run_log: the series was asked for at zero, where the value is exact"
  if 2 * u ^ 2 > v ^ 2 then
    throwError "run_log: the argument {u}/{v} is too large for the remainder bound"
  -- the shortest length whose remainder sits under one unit of the scale
  let mut N := 1
  while 4 * u ^ (2 * N + 1) * S > v ^ (2 * N + 1) do
    N := N + 1
  let pf := fun k ↦ u ^ 2 * (2 * k + 1)
  let qf := fun k ↦ v ^ 2 * (2 * k + 3)
  let p := mkApp (mkConst ``artanhP) (mkRawNatLit u)
  let q := mkApp (mkConst ``artanhQ) (mkRawNatLit v)
  let (T, Q, P, hsplit) ← proveSplit p q pf qf 0 (N - 1)
  let M := 2 * (u * (Q + T)) * S
  let D := v * Q
  if M < D then
    throwError "run_log: the value at {u}/{v} is under one unit of the scale"
  let lo := M / D - 1
  let hi := (M + D + D - 1) / D
  let rb := Lean.reflBoolTrue
  let lit := mkRawNatLit
  let proof := mkAppN (mkConst ``logEnclosure_of_split)
    #[lit u, lit v, lit N, lit (N - 1), lit T, lit Q, lit P, lit (v + u), lit (v - u),
      lit lo, lit hi, lit S, rb, rb, rb, rb, rb, rb, rb, rb, hsplit, rb, rb, rb]
  return (lo, hi, proof)

/-- `log 2`, from the series at `1/3`. -/
meta def proveLogTwo (S : Nat) : MetaM (Nat × Nat × Expr) := do
  let (lo, hi, h) ← proveSeries 1 3 S
  let proof := mkAppN (mkConst ``logEnclosure_of_eq)
    #[mkRawNatLit 4, mkRawNatLit 2, mkRawNatLit 2, mkRawNatLit 1, mkRawNatLit lo, mkRawNatLit hi,
      mkRawNatLit S, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, h]
  return (lo, hi, proof)

/-- `log (n/d)` at scale `S`, by halving the argument into `[1, 2)` and paying for each halving
with a copy of `log 2`. The proof of `log 2` is taken as given, so that one emitted declaration
serves every logarithm at this scale. -/
meta def proveLog (n d S l₂ h₂ : Nat) (htwo : Expr) : MetaM (Nat × Nat × Expr) := do
  if n == 0 || d == 0 then
    throwError "run_log: the argument {n}/{d} is not positive"
  if n < d then
    throwError "run_log: the argument {n}/{d} is under one, where this states nothing"
  -- the halvings that bring the argument into `[1, 2)`
  let mut k := 0
  while n ≥ d * 2 ^ (k + 1) do
    k := k + 1
  let b := d * 2 ^ k
  let rb := Lean.reflBoolTrue
  let lit := mkRawNatLit
  let (lo, hi, hr) ←
    if n == b then
      pure (0, 0, mkApp2 (mkConst ``logEnclosure_one) (lit n) (lit S))
    else do
      let (u, v) := (n - b, n + b)
      let (lo, hi, h) ← proveSeries u v S
      -- the series gave `(v+u)/(v-u)`, which is `2n` over `2b`
      let h' := mkAppN (mkConst ``logEnclosure_of_eq)
        #[lit (v + u), lit (v - u), lit n, lit b, lit lo, lit hi, lit S, rb, rb, rb, h]
      pure (lo, hi, h')
  let lo' := lo + k * l₂
  let hi' := hi + k * h₂
  let proof := mkAppN (mkConst ``logEnclosure_shift)
    #[lit n, lit d, lit k, lit lo, lit hi, lit l₂, lit h₂, lit lo', lit hi', lit S,
      rb, rb, hr, htwo, rb, rb]
  return (lo', hi', proof)

/-- Emit `logTwo_{e}` if it is not already in scope, and return what it says. -/
meta def ensureLogTwo (ns : Name) (scaleExp S : Nat) : MetaM (Nat × Nat × Name) := do
  let name := ns ++ Name.mkSimple s!"logTwo_{scaleExp}"
  match (← getEnv).find? name with
  | some info =>
    let args := info.type.getAppArgs
    match args[2]?.bind Expr.rawNatLit?, args[3]?.bind Expr.rawNatLit? with
    | some lo, some hi => return (lo, hi, name)
    | _, _ => throwError "run_log: {name} does not carry its two ends"
  | none =>
    let (lo, hi, proof) ← proveLogTwo S
    addThm name (mkLogType 2 1 lo hi S) proof
    return (lo, hi, name)

/-- `run_log n d e` emits the enclosure of `log (n/d)` at scale `10 ^ e`. -/
meta def runLog (n d scaleExp : Nat) : MetaM Unit := do
  let S := 10 ^ scaleExp
  let ns ← getCurrNamespace
  let (l₂, h₂, twoName) ← ensureLogTwo ns scaleExp S
  let (lo, hi, proof) ← proveLog n d S l₂ h₂ (mkConst twoName)
  let name := ns ++ Name.mkSimple s!"logEnc_{n}_{d}_{scaleExp}"
  addThm name (mkLogType n d lo hi S) proof
  logInfo s!"run_log: log {n}/{d} in [{lo}, {hi}] over {S}, from {twoName}, as {name}"

/-- `run_log n d e` states `log (n/d)` between two integers over `10 ^ e` (see `runLog`). -/
elab "run_log" nStx:num dStx:num eStx:num : command =>
  liftTermElabM <| runLog nStx.getNat dStx.getNat eStx.getNat

end PrimeCert.LogEmit
