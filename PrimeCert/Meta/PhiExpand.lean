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

/-- `n ≤ m` for two literals, by the `Bool` comparison the kernel decides. `0 < n` is `1 ≤ n`, so
this serves for both. -/
meta def mkLe (n m : Nat) : Expr :=
  mkApp3 (mkConst ``Nat.le_of_ble_eq_true) (mkRawNatLit n) (mkRawNatLit m) Lean.reflBoolTrue

/-- Add `name : type := value` as a theorem. -/
meta def addNodeThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Walk the recurrence from `(t, B)` and emit a declaration for every node, returning the one
at the root. Nodes already emitted are reused. -/
meta partial def emitNode (S : Nat) (ns : Name) (tag : String) (cut : Nat) (dry : Bool)
    (missing : IO.Ref (Std.HashSet (Nat × Nat)))
    (seen : IO.Ref (Std.HashMap (Nat × Nat) Node)) (t B : Nat) : MetaM Node := do
  if let some n := (← seen.get)[(t, B)]? then return n
  -- below the cut a branch stops and is answered from outside, by a leaf the sieve produced
  -- a bound below 3 sieves out almost nothing, and the leaf machinery wants survivors coprime to
  -- 6, so such a branch is expanded rather than cut
  if cut != 0 && t < cut && B ≥ 3 then
    let leafName := ns ++ Name.mkSimple s!"phiLeaf_{t}_{B}"
    match (← getEnv).find? leafName with
    | some info =>
      let args := info.type.getAppArgs
      match args[2]?.bind Expr.rawNatLit?, args[3]?.bind Expr.rawNatLit? with
      | some lo, some hi =>
        let node := { lo, hi, name := leafName }
        seen.modify (·.insert (t, B) node)
        return node
      | _, _ => throwError "run_phi_expand: the leaf {leafName} does not carry its two ends"
    | none =>
      missing.modify (·.insert (t, B))
      let node := { lo := 0, hi := 0, name := leafName }
      seen.modify (·.insert (t, B) node)
      return node
  let name := ns ++ Name.mkSimple s!"phiNode_{tag}_{t}_{B}"
  let emit : Name → Expr → Expr → MetaM Unit := fun nm ty v ↦
    if dry then pure () else addNodeThm nm ty v
  let SE := mkRawNatLit S
  let node ← do
    if t == 0 then
      emit name (mkNodeType 0 B 0 0 S)
        (mkApp2 (mkConst ``phiEnclosure_zero) (mkRawNatLit B) SE)
      pure { lo := 0, hi := 0, name }
    else if t ≤ B then
      emit name (mkNodeType t B S S S)
        (mkAppN (mkConst ``phiEnclosure_one_of_ble)
          #[mkRawNatLit t, mkRawNatLit B, SE, Lean.reflBoolTrue, Lean.reflBoolTrue,
            Lean.reflBoolTrue])
      pure { lo := S, hi := S, name }
    else if B ≤ 1 then
      let a := harmonicFold S t
      emit name (mkNodeType t 1 a (a + t) S)
        (mkAppN (mkConst ``phiEnclosure_of_fold)
          #[mkRawNatLit t, SE, mkRawNatLit a, mkRawNatLit t, Lean.reflBoolTrue,
            mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Nat) (mkRawNatLit a),
            Lean.reflBoolTrue])
      pure { lo := a, hi := a + t, name }
    else if leastFactor B < B then
      let child ← emitNode S ns tag cut dry missing seen t (B - 1)
      emit name (mkNodeType t B child.lo child.hi S)
        (mkAppN (mkConst ``phiEnclosure_step_of_minFac)
          #[mkRawNatLit t, mkRawNatLit (B - 1), mkRawNatLit child.lo, mkRawNatLit child.hi, SE,
            Lean.reflBoolTrue, mkConst child.name])
      pure { lo := child.lo, hi := child.hi, name }
    else
      let left ← emitNode S ns tag cut dry missing seen t (B - 1)
      let right ← emitNode S ns tag cut dry missing seen (t / B) (B - 1)
      let qhi := (right.hi + B - 1) / B
      let qlo := right.lo / B
      if !dry && left.lo < qhi then
        throwError "run_phi_expand: the lower end at {t}, {B} would go below zero"
      if !dry && left.hi < qlo then
        throwError "run_phi_expand: the upper end at {t}, {B} would go below zero"
      let lo := left.lo - qhi
      let hi := left.hi - qlo
      emit name (mkNodeType t B lo hi S)
        (mkAppN (mkConst ``phiEnclosure_split_of_minFac)
          #[mkRawNatLit t, mkRawNatLit B, SE, mkRawNatLit left.lo, mkRawNatLit left.hi,
            mkRawNatLit right.lo, mkRawNatLit right.hi, mkRawNatLit qlo, mkRawNatLit qhi,
            mkRawNatLit lo, mkRawNatLit hi, Lean.reflBoolTrue, Lean.reflBoolTrue,
            Lean.reflBoolTrue, mkConst left.name, mkConst right.name, Lean.reflBoolTrue,
            Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue])
      pure { lo, hi, name }
  seen.modify (·.insert (t, B) node)
  return node

/-- Enclose `phiB x B` by emitting the whole expansion. With `cut` positive, a branch whose height
falls below it stops and is answered by `phiLeaf_{t}_{B}`, which the sieve side supplies; the
command reports any such leaf it cannot find rather than emitting a root that rests on nothing. -/
meta def runPhiExpand (x B scaleExp cut : Nat) : MetaM Unit := do
  let S := 10 ^ scaleExp
  let ns ← getCurrNamespace
  let tag := s!"{x}_{B}_{scaleExp}_{cut}"
  -- walk once without emitting, to see whether every leaf a cut branch wants is in scope
  let probe ← IO.mkRef {}
  let probeMissing ← IO.mkRef {}
  let _ ← emitNode S ns tag cut true probeMissing probe x B
  let want := (← probeMissing.get).toList
  if !want.isEmpty then
    let shown := want.take 8
    logInfo s!"run_phi_expand: {want.length} leaves wanted before this can close, \
{(← probe.get).size} nodes walked. First few, as height and bound: {shown}"
    return
  let seen ← IO.mkRef {}
  let missing ← IO.mkRef {}
  let root ← emitNode S ns tag cut false missing seen x B
  logInfo s!"run_phi_expand: phiB {x} {B} in [{root.lo}, {root.hi}] over {S}, \
{(← seen.get).size} nodes, root {root.name}"

/-- Emit `phiLeaf_{t}_{B}`, the value a cut branch waits on, for a leaf whose height lies below
the square of its bound. There the survivors above `B` are the primes up to `t`, so the whole
range is the difference of two runs of the base sieve and no segment is wanted. The two runs must
already be in scope, from `run_harmonic t e batch` and `run_harmonic B e batch`. -/
meta def runPhiLeaf (t B scaleExp batch : Nat) : MetaM Unit := do
  if B < 3 then
    throwError "run_phi_leaf: the bound {B} is below 3, so the wheel cannot name its survivors"
  if t + 1 > B * B then
    throwError "run_phi_leaf: the height {t} is at or above {B * B}, so this leaf wants a segment"
  if t < B then
    throwError "run_phi_leaf: the height {t} is below the bound {B}, so the value is 1"
  let S := 10 ^ scaleExp
  let ns ← getCurrNamespace
  let env ← getEnv
  let read := fun (bound : Nat) ↦ do
    let nm := `PrimeCert ++ Name.mkSimple s!"primeRecipIcc_{bound}_{scaleExp}_{batch}"
    let some info := env.find? nm
      | throwError "run_phi_leaf: no enclosure {nm}; run `run_harmonic {bound} {scaleExp} \
{batch}` above this command"
    let some args := info.type.getAppArgs[1:3] |>.toArray.mapM Expr.rawNatLit?
      | throwError "run_phi_leaf: the enclosure {nm} does not carry its two numerals"
    pure (args[0]!, args[1]!, nm)
  let (a₁, c₁, n₁) ← read t
  let (a₂, c₂, n₂) ← read B
  if a₁ < a₂ + c₂ then
    throwError "run_phi_leaf: the two runs do not differ in the direction the leaf needs"
  let lo := a₁ - a₂ - c₂
  let cnt := c₁ + c₂
  let lowEnd := S + lo
  let highEnd := S + lo + cnt
  let SE := mkRawNatLit S
  let tE := mkRawNatLit t
  let BE := mkRawNatLit B
  -- the survivors from B+1 to t, as the difference of the two runs
  let mid := mkAppN (mkConst ``sievedRecipRange_of_two_icc)
    #[tE, BE, mkRawNatLit a₁, mkRawNatLit c₁, mkRawNatLit a₂, mkRawNatLit c₂, mkRawNatLit lo,
      mkRawNatLit cnt, SE, mkLe 1 B, mkLe B t, mkLe (t + 1) (B * B),
      mkConst n₁, mkConst n₂, Lean.reflBoolTrue, Lean.reflBoolTrue]
  -- nothing at or below B survives it, so the range from 5 joins on with both totals unchanged
  let whole := mkAppN (mkConst ``sievedRecipRange_add)
    #[mkRawNatLit 5, mkRawNatLit (B + 1), mkRawNatLit (t + 1), BE, mkRawNatLit 0, mkRawNatLit 0,
      mkRawNatLit lo, mkRawNatLit cnt, mkRawNatLit lo, mkRawNatLit cnt, SE,
      Lean.reflBoolTrue, Lean.reflBoolTrue,
      mkAppN (mkConst ``sievedRecipRange_below)
        #[mkRawNatLit (B + 1), BE, SE, mkLe (B + 1) (B + 1)],
      mid, Lean.reflBoolTrue, Lean.reflBoolTrue]
  let leafName := ns ++ Name.mkSimple s!"phiLeaf_{t}_{B}"
  addNodeThm leafName (mkNodeType t B lowEnd highEnd S)
    (mkAppN (mkConst ``phiB_mem_Icc_of_range_scaled)
      #[tE, BE, mkRawNatLit lo, mkRawNatLit cnt, SE, mkRawNatLit lowEnd, mkRawNatLit highEnd,
        mkLe 1 t, mkLe 3 B, Lean.reflBoolTrue, whole,
        Lean.reflBoolTrue, Lean.reflBoolTrue])
  logInfo s!"run_phi_leaf: phiB {t} {B} in [{lowEnd}, {highEnd}] over {S}, \
from the runs at {t} and {B}"

/-- `run_phi_leaf t B e batch` emits the leaf a cut branch waits on (see `runPhiLeaf`). -/
elab "run_phi_leaf" tStx:num bStx:num eStx:num cStx:num : command =>
  liftTermElabM <|
    runPhiLeaf tStx.getNat bStx.getNat eStx.getNat cStx.getNat

/-- `run_phi_expand x B e cut` encloses `phiB x B` at scale `10 ^ e`, stopping a branch whose
height falls below `cut` (see `runPhiExpand`). A `cut` of zero expands everything. -/
elab "run_phi_expand" xStx:num bStx:num eStx:num cStx:(num)? : command =>
  liftTermElabM <|
    runPhiExpand xStx.getNat bStx.getNat eStx.getNat
      (match cStx with | none => 0 | some c => c.getNat)

end PrimeCert.PhiExpand
