/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.PrimeHarmonic
public meta import PrimeCert.Meta.SieveCache

/-! # The `run_harmonic` command

`run_harmonic N e len` encloses `∑ p ≤ N, 1/p` at scale `10 ^ e`, in batches of `len` wheel
positions. It emits one kernel-checked checkpoint per batch for each of the two folds, chains the
checkpoints with `sumB_seed` / `sumB_chain` / `sumB_last`, and applies `primeRecipIcc_of` to the
two chained equations to land `PrimeRecipIcc N A C S`.

The batch literals come from a compiled twin. Unlike the twins in `PrimeCert.Sieve`, this one does
not mirror the kernel definition's operations: it runs its own wheel sieve over a `ByteArray`
rather than reading bits out of the sieve numeral. It does not need to mirror anything, because
the checkpoint is `Nat.beq (acc + sumB f start len 1) acc' = true` closed by `reflBoolTrue`, so a
literal the kernel disagrees with is rejected at `addDecl`.
-/

namespace PrimeCert

open Lean Elab Command Meta

/-! ## The compiled twin -/

/-- `Sieve.value` as the twin computes it: the number at mod-6 wheel position `k`. -/
meta def twinValue (k : Nat) : Nat := (k * 3 + 1) + k % 2

/-- `Sieve.index` as the twin computes it. -/
meta def twinIndex (q : Nat) : Nat := (q - 1) / 3

/-- Byte `t` is `1` exactly when `twinValue t` is prime, for `t ≤ len`. A wheel sieve: the
coprime-to-6 multiples of `p` sit at the positions `index (5*p) + 2*p*j` and `index (7*p) + 2*p*j`,
the same two seeds and the same stride that `buildMaskK` uses. -/
meta def wheelMarks (len : Nat) : ByteArray := Id.run do
  let mut mark := ByteArray.emptyWithCapacity (len + 1)
  for _ in [0:len + 1] do
    mark := mark.push 1
  mark := mark.set! 0 0
  let top := twinValue len
  for t in [1:len + 1] do
    let p := twinValue t
    if p * p > top then
      break
    if mark.get! t == 1 then
      for seed in [twinIndex (5 * p), twinIndex (7 * p)] do
        if seed ≤ len then
          for j in [0:(len - seed) / (2 * p) + 1] do
            mark := mark.set! (seed + 2 * p * j) 0
  return mark

/-- The running totals of the reciprocal fold and the count fold at the end of each batch. -/
meta def twinBatches (mark : ByteArray) (S len batch : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut accA := 0
  let mut accC := 0
  for i in [0:(len + batch - 1) / batch] do
    let start := 1 + i * batch
    for j in [0:Nat.min batch (len - i * batch)] do
      let t := start + j
      if mark.get! t == 1 then
        accA := accA + S / twinValue t
        accC := accC + 1
    out := out.push (accA, accC)
  return out

/-! ## Emitting the chain -/

/-- The proposition `b = true`, for `b : Bool`. -/
meta def mkEqTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- The application `sumB f start len step`, with the three numerals as literals. -/
meta def mkSumB (fE : Expr) (start len step : Nat) : Expr :=
  mkAppN (mkConst ``sumB) #[fE, mkRawNatLit start, mkRawNatLit len, mkRawNatLit step]

/-- Add `name : type := value` to the environment as a theorem. -/
meta def addHarmonicThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Emit one checkpoint per batch for the fold of `fE` over the positions `1 … len`, and return
the total together with a chained proof of `sumB fE 1 len 1 = <total>`. Each checkpoint is its own
declaration, so its kernel reduction covers one batch. -/
meta def emitHarmonicChain (parent : Name) (fE : Expr) (len batch : Nat) (totals : Array Nat) :
    MetaM (Nat × Expr) := do
  let env ← getEnv
  let oneE := mkRawNatLit 1
  let lhs := mkSumB fE 1 len 1
  let mut accE := mkRawNatLit 0
  let mut acc := 0
  let mut proof := mkAppN (mkConst ``sumB_seed) #[fE, oneE, mkRawNatLit len, oneE]
  for i in [0:(len + batch - 1) / batch] do
    let start := 1 + i * batch
    let owed := len - i * batch
    let stepN := Nat.min batch owed
    let some next := totals[i]? | throwError "run_harmonic: the twin is short of batch {i}"
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
    addHarmonicThm stepName
      (mkEqTrue (mkApp2 (mkConst ``Nat.beq)
        (mkApp2 (mkConst ``Nat.add) accE (mkSumB fE start stepN 1)) (mkRawNatLit next)))
      Lean.reflBoolTrue
    proof := if owed == stepN then
        mkAppN (mkConst ``sumB_last)
          #[fE, lhs, mkRawNatLit start, oneE, mkRawNatLit stepN, accE, mkRawNatLit next,
            proof, mkConst stepName]
      else
        mkAppN (mkConst ``sumB_chain)
          #[fE, lhs, mkRawNatLit start, oneE, mkRawNatLit stepN, mkRawNatLit (owed - stepN),
            accE, mkRawNatLit next, proof, mkConst stepName]
    acc := next
    accE := mkRawNatLit next
  return (acc, proof)

/-! ## The command -/

/-- Enclose `∑ p ≤ bound, 1/p` at scale `10 ^ scaleExp`, in batches of `batch` wheel positions.
Emits `harmonicFold_…`, `harmonicCount_…` and `primeRecipIcc_…`, the last of type
`PrimeRecipIcc bound A C S`. -/
meta def runHarmonic (bound scaleExp batch : Nat) : MetaM Unit := do
  if bound < 5 then
    throwError "run_harmonic: the bound must be at least 5"
  let batch := Nat.max 1 batch
  let some cache ← Sieve.findSieveCache bound
    | throwError "run_harmonic: no sieve cache in scope covers {bound}"
  let S := 10 ^ scaleExp
  let mut len := twinIndex bound
  for _ in [0:2] do
    if twinValue len > bound then
      len := len - 1
  if len == 0 || twinValue len > bound || twinValue (len + 1) ≤ bound then
    throwError "run_harmonic: could not place the last wheel position inside {bound}"
  let batches := twinBatches (wheelMarks len) S len batch
  let sE := mkConst cache.litName
  let fRecip := mkApp2 (mkConst ``recipAtK) sE (mkRawNatLit S)
  let fCount := mkApp (mkConst ``bitAtK) sE
  let tag := s!"{bound}_{scaleExp}_{batch}"
  let foldName := `PrimeCert ++ Name.mkSimple s!"harmonicFold_{tag}"
  let countName := `PrimeCert ++ Name.mkSimple s!"harmonicCount_{tag}"
  let iccName := `PrimeCert ++ Name.mkSimple s!"primeRecipIcc_{tag}"
  let (aTot, aProof) ← emitHarmonicChain foldName fRecip len batch (batches.map (·.1))
  addHarmonicThm foldName (mkNatEq (mkSumB fRecip 1 len 1) (mkRawNatLit aTot)) aProof
  let (cTot, cProof) ← emitHarmonicChain countName fCount len batch (batches.map (·.2))
  addHarmonicThm countName (mkNatEq (mkSumB fCount 1 len 1) (mkRawNatLit cTot)) cProof
  let iccProof := mkAppN (mkConst ``primeRecipIcc_of)
    #[mkRawNatLit cache.hi, mkRawNatLit bound, mkRawNatLit S, sE, mkRawNatLit len,
      mkRawNatLit aTot, mkRawNatLit cTot, mkConst cache.isSieveName,
      Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
      Lean.reflBoolTrue, mkConst foldName, mkConst countName]
  addHarmonicThm iccName
    (mkAppN (mkConst ``PrimeRecipIcc)
      #[mkRawNatLit bound, mkRawNatLit aTot, mkRawNatLit cTot, mkRawNatLit S])
    iccProof
  logInfo s!"run_harmonic {bound}: {len} positions, {(len + batch - 1) / batch} batches of \
{batch}, sieve {cache.litName}; A = {aTot}, C = {cTot}"

/-- `run_harmonic bound e len` encloses the sum of the reciprocals of the primes up to `bound`, at
scale `10 ^ e`, with the fold cut into batches of `len` wheel positions. -/
elab "run_harmonic" bStx:num eStx:num lStx:num : command =>
  liftTermElabM <| runHarmonic bStx.getNat eStx.getNat lStx.getNat

/-! ## Splitting the fold by residue class of the position -/

/-- The running totals of the reciprocal fold and the count fold at the end of each batch of the
run of `len` positions `start, start + step, …`. -/
meta def twinRunBatches (mark : ByteArray) (S start len step batch : Nat) :
    Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut accA := 0
  let mut accC := 0
  for i in [0:(len + batch - 1) / batch] do
    for j in [0:Nat.min batch (len - i * batch)] do
      let t := start + (i * batch + j) * step
      if mark.get! t == 1 then
        accA := accA + S / twinValue t
        accC := accC + 1
    out := out.push (accA, accC)
  return out

/-- Emit one checkpoint per batch for the fold of `fE` over the run of `len` positions stepping by
`step` from `start`, whose first position the statement writes as `startE`, and return the total
with a chained proof of `sumB fE startE len step = <total>`. -/
meta def emitRunChain (parent : Name) (fE startE : Expr) (start len step batch : Nat)
    (totals : Array Nat) : MetaM (Nat × Expr) := do
  let env ← getEnv
  let stepE := mkRawNatLit step
  let lhs := mkAppN (mkConst ``sumB) #[fE, startE, mkRawNatLit len, stepE]
  let mut accE := mkRawNatLit 0
  let mut acc := 0
  let mut proof := mkAppN (mkConst ``sumB_seed) #[fE, startE, mkRawNatLit len, stepE]
  for i in [0:(len + batch - 1) / batch] do
    let cur := start + i * batch * step
    let curE := if i == 0 then startE else mkRawNatLit cur
    let owed := len - i * batch
    let stepN := Nat.min batch owed
    let some next := totals[i]? | throwError "run_harmonic_classes: the twin is short of batch {i}"
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
    addHarmonicThm stepName
      (mkEqTrue (mkApp2 (mkConst ``Nat.beq)
        (mkApp2 (mkConst ``Nat.add) accE (mkSumB fE cur stepN step)) (mkRawNatLit next)))
      Lean.reflBoolTrue
    proof := if owed == stepN then
        mkAppN (mkConst ``sumB_last)
          #[fE, lhs, curE, stepE, mkRawNatLit stepN, accE, mkRawNatLit next, proof,
            mkConst stepName]
      else
        mkAppN (mkConst ``sumB_chain)
          #[fE, lhs, curE, stepE, mkRawNatLit stepN, mkRawNatLit (owed - stepN), accE,
            mkRawNatLit next, proof, mkConst stepName]
    acc := next
    accE := mkRawNatLit next
  return (acc, proof)

/-- Emit one fold split into the `C` position classes modulo `C`, each a run of `L` positions, and
the `R` positions left over, and declare `foldName : sumB fE 1 len 1 = <total>`. The count fold
takes the second component of the twin's totals, the reciprocal fold the first. -/
meta def emitClassFold (foldName : Name) (fE : Expr) (mark : ByteArray) (S C L R len batch : Nat)
    (useCount : Bool) : MetaM Nat := do
  let pick : Nat × Nat → Nat := fun p ↦ if useCount then p.2 else p.1
  let oneE := mkRawNatLit 1
  let CE := mkRawNatLit C
  let LE := mkRawNatLit L
  let mut accE := mkRawNatLit 0
  let mut acc := 0
  let mut proof := mkAppN (mkConst ``classAcc_zero) #[fE, oneE, LE, CE]
  for k in [0:C] do
    let kE := mkRawNatLit k
    let startE := mkApp2 (mkConst ``Nat.add) kE oneE
    let totals := (twinRunBatches mark S (k + 1) L C batch).map pick
    let className := foldName ++ Name.mkSimple s!"class_{k}"
    let (a, aProof) ← emitRunChain className fE startE (k + 1) L C batch totals
    addHarmonicThm className
      (mkNatEq (mkAppN (mkConst ``sumB) #[fE, startE, LE, CE]) (mkRawNatLit a)) aProof
    let next := acc + a
    proof := mkAppN (mkConst ``classAcc_step)
      #[fE, oneE, LE, CE, kE, accE, mkRawNatLit a, mkRawNatLit next, proof, mkConst className,
        Lean.reflBoolTrue]
    acc := next
    accE := mkRawNatLit next
  let accName := foldName ++ `classes
  addHarmonicThm accName
    (mkNatEq (mkAppN (mkConst ``classAcc) #[fE, oneE, LE, CE, CE]) (mkRawNatLit acc)) proof
  let remStartE := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.mul) CE LE) oneE
  let (r, rProof) ← if R == 0 then
      pure (0, mkAppN (mkConst ``sumB_zero) #[fE, remStartE, oneE])
    else
      emitRunChain (foldName ++ `rest) fE remStartE (C * L + 1) R 1 batch
        ((twinRunBatches mark S (C * L + 1) R 1 batch).map pick)
  let remName := foldName ++ `rest_total
  addHarmonicThm remName
    (mkNatEq (mkAppN (mkConst ``sumB) #[fE, remStartE, mkRawNatLit R, oneE]) (mkRawNatLit r))
    rProof
  let total := acc + r
  addHarmonicThm foldName
    (mkNatEq (mkSumB fE 1 len 1) (mkRawNatLit total))
    (mkAppN (mkConst ``sumB_classSplit_close)
      #[fE, CE, LE, mkRawNatLit R, mkRawNatLit acc, mkRawNatLit r, mkRawNatLit total,
        mkConst accName, mkConst remName, Lean.reflBoolTrue])
  return total

/-- Enclose `∑ p ≤ bound, 1/p` as `run_harmonic` does, with each fold split into the `C` residue
classes of the position modulo `C`, every class cut into batches of `batch` positions. -/
meta def runHarmonicClasses (bound scaleExp C batch : Nat) : MetaM Unit := do
  if bound < 5 then
    throwError "run_harmonic_classes: the bound must be at least 5"
  if C == 0 then
    throwError "run_harmonic_classes: the number of classes must be positive"
  let batch := Nat.max 1 batch
  let some cache ← Sieve.findSieveCache bound
    | throwError "run_harmonic_classes: no sieve cache in scope covers {bound}"
  let S := 10 ^ scaleExp
  let mut len := twinIndex bound
  for _ in [0:2] do
    if twinValue len > bound then
      len := len - 1
  if len == 0 || twinValue len > bound || twinValue (len + 1) ≤ bound then
    throwError "run_harmonic_classes: could not place the last wheel position inside {bound}"
  let L := len / C
  let R := len % C
  if L == 0 then
    throwError "run_harmonic_classes: {len} positions is fewer than {C} classes"
  let mark := wheelMarks len
  let sE := mkConst cache.litName
  let fRecip := mkApp2 (mkConst ``recipAtK) sE (mkRawNatLit S)
  let fCount := mkApp (mkConst ``bitAtK) sE
  let tag := s!"{bound}_{scaleExp}_{C}_{batch}"
  let foldName := `PrimeCert ++ Name.mkSimple s!"harmonicClassFold_{tag}"
  let countName := `PrimeCert ++ Name.mkSimple s!"harmonicClassCount_{tag}"
  let iccName := `PrimeCert ++ Name.mkSimple s!"primeRecipIccClasses_{tag}"
  let aTot ← emitClassFold foldName fRecip mark S C L R len batch false
  let cTot ← emitClassFold countName fCount mark S C L R len batch true
  let iccProof := mkAppN (mkConst ``primeRecipIcc_of)
    #[mkRawNatLit cache.hi, mkRawNatLit bound, mkRawNatLit S, sE, mkRawNatLit len,
      mkRawNatLit aTot, mkRawNatLit cTot, mkConst cache.isSieveName,
      Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
      Lean.reflBoolTrue, mkConst foldName, mkConst countName]
  addHarmonicThm iccName
    (mkAppN (mkConst ``PrimeRecipIcc)
      #[mkRawNatLit bound, mkRawNatLit aTot, mkRawNatLit cTot, mkRawNatLit S])
    iccProof
  logInfo s!"run_harmonic_classes {bound}: {len} positions in {C} classes of {L} plus {R}, \
batches of {batch}, sieve {cache.litName}; A = {aTot}, C = {cTot}"

/-- `run_harmonic_classes bound e C len` encloses the sum of the reciprocals of the primes up to
`bound` at scale `10 ^ e`, with each fold split into the `C` residue classes of the position modulo
`C` and every class cut into batches of `len` positions. -/
elab "run_harmonic_classes" bStx:num eStx:num cStx:num lStx:num : command =>
  liftTermElabM <| runHarmonicClasses bStx.getNat eStx.getNat cStx.getNat lStx.getNat

end PrimeCert
