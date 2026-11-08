/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.Phi

/-!
# Emitting a whole expansion

`run_phi_expand x B e` encloses `phiB x B` at scale `10 ^ e` by walking the recurrence and
emitting one declaration per node: a branch at each prime, a step past each composite, and at the
bottom either a known value or the fold of the rounded reciprocals. Nodes are shared, so a height
and bound reached twice is stated once.

This is the small-target form. A real target's harmonic leaves sit at heights where the fold is
out of reach and a logarithm is wanted; `PrimeCert/PhiLog.lean` states that leaf and waits on
numerals. Here the fold serves, so the whole method runs at a size that can be checked by hand.
-/

namespace PrimeCert.PhiExpand

open Lean Elab Command Meta

/-- One node of the expansion: its two scaled ends and the declaration proving them. -/
meta structure Node where
  lo : Nat
  hi : Nat
  name : Name
  deriving Inhabited

/-- `sumB (recipPlain S) 1 t 1`, the fold the harmonic leaf is enclosed by. -/
meta def harmonicFold (S t : Nat) : Nat := Id.run do
  let mut acc := 0
  for n in [1:t + 1] do
    acc := acc + S / n
  return acc

/-- The least prime factor, as the kernel will compute it. -/
meta def leastFactor (n : Nat) : Nat := Id.run do
  if n < 2 then return n
  let mut d := 2
  while d * d ≤ n do
    if n % d == 0 then return d
    d := d + 1
  return n

/-- The statement a node carries, every number a literal. -/
meta def mkNodeType (t B lo hi S : Nat) : Expr :=
  mkAppN (mkConst ``PhiEnclosure)
    #[mkRawNatLit t, mkRawNatLit B, mkRawNatLit lo, mkRawNatLit hi, mkRawNatLit S]

/-- Add `name : type := value` as a theorem. -/
meta def addNodeThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Walk the recurrence from `(t, B)` and emit a declaration for every node, returning the one
at the root. Nodes already emitted are reused. -/
meta partial def emitNode (S : Nat) (ns : Name) (seen : IO.Ref (Std.HashMap (Nat × Nat) Node))
    (t B : Nat) : MetaM Node := do
  if let some n := (← seen.get)[(t, B)]? then return n
  let name := ns ++ Name.mkSimple s!"phiNode_{t}_{B}"
  let SE := mkRawNatLit S
  let node ← do
    if t == 0 then
      addNodeThm name (mkNodeType 0 B 0 0 S)
        (mkApp2 (mkConst ``phiEnclosure_zero) (mkRawNatLit B) SE)
      pure { lo := 0, hi := 0, name }
    else if t ≤ B then
      addNodeThm name (mkNodeType t B S S S)
        (mkAppN (mkConst ``phiEnclosure_one_of_ble)
          #[mkRawNatLit t, mkRawNatLit B, SE, Lean.reflBoolTrue, Lean.reflBoolTrue,
            Lean.reflBoolTrue])
      pure { lo := S, hi := S, name }
    else if B ≤ 1 then
      let a := harmonicFold S t
      addNodeThm name (mkNodeType t 1 a (a + t) S)
        (mkAppN (mkConst ``phiEnclosure_of_fold)
          #[mkRawNatLit t, SE, mkRawNatLit a, mkRawNatLit t, Lean.reflBoolTrue,
            mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkRawNatLit a),
            Lean.reflBoolTrue])
      pure { lo := a, hi := a + t, name }
    else if leastFactor B < B then
      let child ← emitNode S ns seen t (B - 1)
      addNodeThm name (mkNodeType t B child.lo child.hi S)
        (mkAppN (mkConst ``phiEnclosure_step_of_minFac)
          #[mkRawNatLit t, mkRawNatLit (B - 1), mkRawNatLit child.lo, mkRawNatLit child.hi, SE,
            Lean.reflBoolTrue, mkConst child.name])
      pure { lo := child.lo, hi := child.hi, name }
    else
      let left ← emitNode S ns seen t (B - 1)
      let right ← emitNode S ns seen (t / B) (B - 1)
      let qhi := (right.hi + B - 1) / B
      let qlo := right.lo / B
      if left.lo < qhi then
        throwError "run_phi_expand: the lower end at {t}, {B} would go below zero"
      if left.hi < qlo then
        throwError "run_phi_expand: the upper end at {t}, {B} would go below zero"
      let lo := left.lo - qhi
      let hi := left.hi - qlo
      addNodeThm name (mkNodeType t B lo hi S)
        (mkAppN (mkConst ``phiEnclosure_split_of_minFac)
          #[mkRawNatLit t, mkRawNatLit B, SE, mkRawNatLit left.lo, mkRawNatLit left.hi,
            mkRawNatLit right.lo, mkRawNatLit right.hi, mkRawNatLit qlo, mkRawNatLit qhi,
            mkRawNatLit lo, mkRawNatLit hi, Lean.reflBoolTrue, Lean.reflBoolTrue,
            Lean.reflBoolTrue, mkConst left.name, mkConst right.name, Lean.reflBoolTrue,
            Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue])
      pure { lo, hi, name }
  seen.modify (·.insert (t, B) node)
  return node

/-- Enclose `phiB x B` by emitting the whole expansion. -/
meta def runPhiExpand (x B scaleExp : Nat) : MetaM Unit := do
  let S := 10 ^ scaleExp
  let ns ← getCurrNamespace
  let seen ← IO.mkRef {}
  let root ← emitNode S ns seen x B
  let count := (← seen.get).size
  logInfo s!"run_phi_expand: phiB {x} {B} in [{root.lo}, {root.hi}] over {S}, \
{count} nodes, root {root.name}"

/-- `run_phi_expand x B e` encloses `phiB x B` at scale `10 ^ e` (see `runPhiExpand`). -/
elab "run_phi_expand" xStx:num bStx:num eStx:num : command =>
  liftTermElabM <| runPhiExpand xStx.getNat bStx.getNat eStx.getNat

end PrimeCert.PhiExpand
