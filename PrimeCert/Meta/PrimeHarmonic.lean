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

/-- The resident memory of this process in kibibytes, read from `/proc/self/status`, or `0` where
that file is unavailable. -/
meta def rssKb : IO Nat := do
  let s ← try IO.FS.readFile "/proc/self/status" catch _ => pure ""
  for line in s.splitOn "\n" do
    if line.startsWith "VmRSS:" then
      return (String.ofList (line.toList.filter Char.isDigit)).toNat!
  return 0

/-- When the environment variable `PRIMECERT_PROGRESS` is set, write one line to stderr with the
elapsed monotonic time and the resident memory, flushed at once so that it survives an abort. -/
meta def progress (msg : String) : IO Unit := do
  if (← IO.getEnv "PRIMECERT_PROGRESS").isSome then
    let e ← IO.getStderr
    e.putStrLn s!"[progress {← IO.monoMsNow} ms, rss {← rssKb} KB] {msg}"
    e.flush

/-- Emit one fold split into the `C` position classes modulo `C`, each a run of `L` positions, and
the `R` positions left over, and declare `foldName : sumB fE 1 len 1 = <total>`. `pick` turns the
twin's pair of totals (reciprocal, count) into this fold's total. The class totals are added in two
levels: blocks of about `√C` classes, each block its own theorem, then the blocks. -/
meta def emitClassFold (foldName : Name) (fE : Expr) (mark : ByteArray) (S C L R len batch : Nat)
    (pick : Nat × Nat → Nat) : MetaM Nat := do
  let oneE := mkRawNatLit 1
  let CE := mkRawNatLit C
  let LE := mkRawNatLit L
  let D := Nat.sqrt C + 1
  let mut accE := mkRawNatLit 0
  let mut acc := 0
  let mut proof := mkAppN (mkConst ``classAcc_zero) #[fE, oneE, LE, CE]
  for b in [0:(C + D - 1) / D] do
    let a := b * D
    let n := Nat.min D (C - a)
    let aE := mkRawNatLit a
    let mut bAccE := mkRawNatLit 0
    let mut bAcc := 0
    let mut bProof := mkAppN (mkConst ``classBlock_zero) #[fE, oneE, LE, CE, aE]
    for i in [0:n] do
      let k := a + i
      progress s!"{foldName} class {k}: start"
      let iE := mkRawNatLit i
      let startE := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) aE iE) oneE
      let totals := (twinRunBatches mark S (k + 1) L C batch).map pick
      let className := foldName ++ Name.mkSimple s!"class_{k}"
      let (x, xProof) ← emitRunChain className fE startE (k + 1) L C batch totals
      addHarmonicThm className
        (mkNatEq (mkAppN (mkConst ``sumB) #[fE, startE, LE, CE]) (mkRawNatLit x)) xProof
      progress s!"{foldName} class {k}: declared"
      let next := bAcc + x
      bProof := mkAppN (mkConst ``classBlock_step)
        #[fE, oneE, LE, CE, aE, iE, bAccE, mkRawNatLit x, mkRawNatLit next, bProof,
          mkConst className, Lean.reflBoolTrue]
      bAcc := next
      bAccE := mkRawNatLit next
    let blockName := foldName ++ Name.mkSimple s!"block_{b}"
    addHarmonicThm blockName
      (mkNatEq (mkAppN (mkConst ``classBlock) #[fE, oneE, LE, CE, aE, mkRawNatLit n])
        (mkRawNatLit bAcc))
      bProof
    let next := acc + bAcc
    proof := mkAppN (mkConst ``classAcc_block)
      #[fE, oneE, LE, CE, aE, mkRawNatLit n, accE, mkRawNatLit bAcc, mkRawNatLit next, proof,
        mkConst blockName, Lean.reflBoolTrue]
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
classes of the position modulo `C`, every class cut into batches of `batch` positions. `folds` is
`2` for the reciprocal and count folds, or `3` for the two packed into one fold. -/
meta def runHarmonicClasses (bound scaleExp C batch folds : Nat) : MetaM Unit := do
  if bound < 5 then
    throwError "run_harmonic_classes: the bound must be at least 5"
  if C == 0 then
    throwError "run_harmonic_classes: the number of classes must be positive"
  if folds != 2 && folds != 3 then
    throwError "run_harmonic_classes: folds must be 2 or 3"
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
  progress s!"run_harmonic_classes {bound}: twin sieve over {len} positions"
  let mark := wheelMarks len
  progress s!"run_harmonic_classes {bound}: twin sieve done, {mark.size} bytes"
  let sE := mkConst cache.litName
  let SE := mkRawNatLit S
  let fRecip := mkApp2 (mkConst ``recipAtK) sE SE
  let fCount := mkApp (mkConst ``bitAtK) sE
  let tag := s!"{bound}_{scaleExp}_{C}_{batch}_{folds}"
  let foldName := `PrimeCert ++ Name.mkSimple s!"harmonicClassFold_{tag}"
  let countName := `PrimeCert ++ Name.mkSimple s!"harmonicClassCount_{tag}"
  let iccName := `PrimeCert ++ Name.mkSimple s!"primeRecipIccClasses_{tag}"
  if folds == 3 then
    let P := len * S + 1
    let PE := mkRawNatLit P
    let fPack := mkApp3 (mkConst ``packAtK) sE SE PE
    let packName := `PrimeCert ++ Name.mkSimple s!"harmonicClassPack_{tag}"
    let T ← emitClassFold packName fPack mark S C L R len batch (fun p ↦ p.1 + P * p.2)
    addHarmonicThm iccName
      (mkAppN (mkConst ``PrimeRecipIcc)
        #[mkRawNatLit bound, mkRawNatLit (T % P), mkRawNatLit (T / P), SE])
      (mkAppN (mkConst ``primeRecipIcc_of_pack)
        #[mkRawNatLit cache.hi, mkRawNatLit bound, SE, PE, sE, mkRawNatLit len, mkRawNatLit T,
          mkConst cache.isSieveName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
          Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst packName])
    logInfo s!"run_harmonic_classes {bound}: {len} positions in {C} classes of {L} plus {R}, \
batches of {batch}, packed fold, sieve {cache.litName}; A = {T % P}, C = {T / P}"
    return
  let aTot ← emitClassFold foldName fRecip mark S C L R len batch (·.1)
  let cTot ← emitClassFold countName fCount mark S C L R len batch (·.2)
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

/-- `run_harmonic_classes bound e C len folds?` encloses the sum of the reciprocals of the primes up
to `bound` at scale `10 ^ e`, with each fold split into the `C` residue classes of the position
modulo `C` and every class cut into batches of `len` positions; `folds` is `2` (the default) or `3`
(packed). -/
elab "run_harmonic_classes" bStx:num eStx:num cStx:num lStx:num fStx:(num)? : command =>
  liftTermElabM <| runHarmonicClasses bStx.getNat eStx.getNat cStx.getNat lStx.getNat
    ((fStx.map (·.getNat)).getD 2)

/-! ## Reading each batch through a window of the sieve -/

/-- One batch of consecutive positions: its first position, its length, the window literal holding
the twin's marks for those positions, and the batch totals of the two folds. -/
structure WindowBatch where
  lo : Nat
  len : Nat
  w : Nat
  recip : Nat
  count : Nat

/-- The empty batch, so that the elaborator can index arrays of batches with `!`. -/
meta instance : Inhabited WindowBatch := ⟨⟨0, 0, 0, 0, 0⟩⟩

/-- The window literal for the positions `lo … lo + n - 1`: bit `i` is the twin's mark at
`lo + i`. -/
meta def twinWindow (mark : ByteArray) (lo n : Nat) : Nat := Id.run do
  let mut w := 0
  for i in [0:n] do
    w := 2 * w + (if mark.get! (lo + n - 1 - i) == 1 then 1 else 0)
  return w

/-- The batches of `B` consecutive positions covering `1 … len`, with their windows and totals. -/
meta def twinWindows (mark : ByteArray) (S len B : Nat) : Array WindowBatch := Id.run do
  let mut out : Array WindowBatch := #[]
  for i in [0:(len + B - 1) / B] do
    let lo := 1 + i * B
    let n := Nat.min B (len - i * B)
    let mut r := 0
    let mut c := 0
    for j in [0:n] do
      if mark.get! (lo + j) == 1 then
        r := r + S / twinValue (lo + j)
        c := c + 1
    out := out.push { lo, len := n, w := twinWindow mark lo n, recip := r, count := c }
  return out

/-- The proposition that `w` is the `B` bits of `sE` from position `lo`. -/
meta def mkWindowEq (sE : Expr) (lo B w : Nat) : Expr :=
  mkEqTrue (mkApp2 (mkConst ``Nat.beq)
    (mkApp2 (mkConst ``Nat.land) (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit lo))
      (mkApp2 (mkConst ``Nat.sub)
        (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit B)) (mkRawNatLit 1)))
    (mkRawNatLit w))

/-- The number of positions in the batches `a … b - 1`. -/
meta def windowSpan (wins : Array WindowBatch) (a b : Nat) : Nat := Id.run do
  let mut n := 0
  for k in [a:b] do
    n := n + wins[k]!.len
  return n

/-- Emit one batch equation per batch `a … b - 1` of one fold, each reading its window, and return
the total with a chained proof of `sumB fE lo n 1 = <total>`, where `lo` is the first position of
batch `a` and `n` the number of positions covered. `gE w lo` is the windowed fold function of a
batch and `bridge lo n w name` its bridge equation from the window theorem `name`. -/
meta def emitWindowRun (parent : Name) (fE : Expr) (gE : Nat → Nat → Expr)
    (bridge : Nat → Nat → Nat → Name → Expr) (pick : WindowBatch → Nat)
    (wins : Array WindowBatch) (winNames : Array Name) (a b : Nat) : MetaM (Nat × Expr) := do
  let env ← getEnv
  let oneE := mkRawNatLit 1
  let zeroE := mkRawNatLit 0
  let lo0 := wins[a]!.lo
  let n := windowSpan wins a b
  let lhs := mkAppN (mkConst ``sumB) #[fE, mkRawNatLit lo0, mkRawNatLit n, oneE]
  let mut accE := zeroE
  let mut acc := 0
  let mut owed := n
  let mut proof := mkAppN (mkConst ``sumB_seed) #[fE, mkRawNatLit lo0, mkRawNatLit n, oneE]
  for k in [a:b] do
    let wb := wins[k]!
    let gw := gE wb.w wb.lo
    let next := acc + pick wb
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{k}")
    addHarmonicThm stepName
      (mkEqTrue (mkApp2 (mkConst ``Nat.beq)
        (mkApp2 (mkConst ``Nat.add) accE
          (mkAppN (mkConst ``sumB) #[gw, zeroE, mkRawNatLit wb.len, oneE]))
        (mkRawNatLit next)))
      Lean.reflBoolTrue
    let hb := bridge wb.lo wb.len wb.w winNames[k]!
    proof := if owed == wb.len then
        mkAppN (mkConst ``sumB_lastVia)
          #[fE, gw, lhs, mkRawNatLit wb.lo, oneE, mkRawNatLit wb.len, accE, mkRawNatLit next,
            proof, hb, mkConst stepName]
      else
        mkAppN (mkConst ``sumB_chainVia)
          #[fE, gw, lhs, mkRawNatLit wb.lo, oneE, mkRawNatLit wb.len,
            mkRawNatLit (owed - wb.len), accE, mkRawNatLit next, proof, hb, mkConst stepName]
    owed := owed - wb.len
    acc := next
    accE := mkRawNatLit next
  return (acc, proof)

/-- Emit one windowed fold over all the batches and declare `foldName : sumB fE 1 len 1 = <total>`.
With `G = 0` the batches form one chain; otherwise they are grouped into segments of `G` batches,
each segment its own theorem, and the segments are chained. -/
meta def emitWindowFold (foldName : Name) (fE : Expr) (gE : Nat → Nat → Expr)
    (bridge : Nat → Nat → Nat → Name → Expr) (pick : WindowBatch → Nat)
    (wins : Array WindowBatch) (winNames : Array Name) (len G : Nat) : MetaM Nat := do
  let nb := wins.size
  let lhs := mkSumB fE 1 len 1
  if G == 0 || nb ≤ G then
    let (tot, proof) ← emitWindowRun foldName fE gE bridge pick wins winNames 0 nb
    addHarmonicThm foldName (mkNatEq lhs (mkRawNatLit tot)) proof
    return tot
  let oneE := mkRawNatLit 1
  let mut accE := mkRawNatLit 0
  let mut acc := 0
  let mut owed := len
  let mut proof := mkAppN (mkConst ``sumB_seed) #[fE, oneE, mkRawNatLit len, oneE]
  for g in [0:(nb + G - 1) / G] do
    let a := g * G
    let b := Nat.min nb (a + G)
    let segName := foldName ++ Name.mkSimple s!"seg_{g}"
    let (segTot, segProof) ← emitWindowRun segName fE gE bridge pick wins winNames a b
    let segLo := wins[a]!.lo
    let segLen := windowSpan wins a b
    addHarmonicThm segName
      (mkNatEq (mkAppN (mkConst ``sumB) #[fE, mkRawNatLit segLo, mkRawNatLit segLen, oneE])
        (mkRawNatLit segTot))
      segProof
    let next := acc + segTot
    proof := if owed == segLen then
        mkAppN (mkConst ``sumB_lastEq)
          #[fE, lhs, mkRawNatLit segLo, oneE, mkRawNatLit segLen, accE, mkRawNatLit segTot,
            mkRawNatLit next, proof, mkConst segName, Lean.reflBoolTrue]
      else
        mkAppN (mkConst ``sumB_chainEq)
          #[fE, lhs, mkRawNatLit segLo, oneE, mkRawNatLit segLen, mkRawNatLit (owed - segLen),
            accE, mkRawNatLit segTot, mkRawNatLit next, proof, mkConst segName,
            Lean.reflBoolTrue]
    owed := owed - segLen
    acc := next
    accE := mkRawNatLit next
  addHarmonicThm foldName (mkNatEq lhs (mkRawNatLit acc)) proof
  return acc

/-- Enclose `∑ p ≤ bound, 1/p` at scale `10 ^ scaleExp` with every batch of `B` consecutive
positions read through its own window of the sieve. `G` groups batches into segments (`0` for one
chain), and `folds` is `2` for the reciprocal and count folds, `1` for the reciprocal fold alone,
which bounds the count by the number of positions, or `3` for the two packed into one fold. -/
meta def runHarmonicWindow (bound scaleExp B G folds : Nat) : MetaM Unit := do
  if bound < 5 then
    throwError "run_harmonic_window: the bound must be at least 5"
  if folds != 1 && folds != 2 && folds != 3 then
    throwError "run_harmonic_window: folds must be 1, 2 or 3"
  let B := Nat.max 1 B
  let some cache ← Sieve.findSieveCache bound
    | throwError "run_harmonic_window: no sieve cache in scope covers {bound}"
  let S := 10 ^ scaleExp
  let mut len := twinIndex bound
  for _ in [0:2] do
    if twinValue len > bound then
      len := len - 1
  if len == 0 || twinValue len > bound || twinValue (len + 1) ≤ bound then
    throwError "run_harmonic_window: could not place the last wheel position inside {bound}"
  let wins := twinWindows (wheelMarks len) S len B
  let sE := mkConst cache.litName
  let SE := mkRawNatLit S
  let tag := s!"{bound}_{scaleExp}_{B}_{G}_{folds}"
  let env ← getEnv
  let winBase := `PrimeCert ++ Name.mkSimple s!"harmonicWindow_{tag}"
  let mut winNames : Array Name := #[]
  for k in [0:wins.size] do
    let wb := wins[k]!
    let nm := mkPrivateName env (winBase ++ Name.mkSimple s!"w_{k}")
    addHarmonicThm nm (mkWindowEq sE wb.lo wb.len wb.w) Lean.reflBoolTrue
    winNames := winNames.push nm
  let fRecip := mkApp2 (mkConst ``recipAtK) sE SE
  let gRecip : Nat → Nat → Expr := fun w lo ↦
    mkApp3 (mkConst ``recipAtW) (mkRawNatLit w) (mkRawNatLit lo) SE
  let bRecip : Nat → Nat → Nat → Name → Expr := fun lo n w nm ↦
    mkAppN (mkConst ``recip_window)
      #[sE, SE, mkRawNatLit lo, mkRawNatLit n, mkRawNatLit w, mkConst nm]
  let iccName := `PrimeCert ++ Name.mkSimple s!"primeRecipIccWindow_{tag}"
  let side := #[mkRawNatLit cache.hi, mkRawNatLit bound, SE, sE, mkRawNatLit len]
  if folds == 3 then
    let P := len * S + 1
    let PE := mkRawNatLit P
    let fPack := mkApp3 (mkConst ``packAtK) sE SE PE
    let gPack : Nat → Nat → Expr := fun w lo ↦
      mkApp4 (mkConst ``packAtW) (mkRawNatLit w) (mkRawNatLit lo) SE PE
    let bPack : Nat → Nat → Nat → Name → Expr := fun lo n w nm ↦
      mkAppN (mkConst ``pack_window)
        #[sE, SE, PE, mkRawNatLit lo, mkRawNatLit n, mkRawNatLit w, mkConst nm]
    let packName := `PrimeCert ++ Name.mkSimple s!"harmonicWindowPack_{tag}"
    let T ← emitWindowFold packName fPack gPack bPack (fun wb ↦ wb.recip + P * wb.count)
      wins winNames len G
    addHarmonicThm iccName
      (mkAppN (mkConst ``PrimeRecipIcc)
        #[mkRawNatLit bound, mkRawNatLit (T % P), mkRawNatLit (T / P), SE])
      (mkAppN (mkConst ``primeRecipIcc_of_pack)
        #[mkRawNatLit cache.hi, mkRawNatLit bound, SE, PE, sE, mkRawNatLit len, mkRawNatLit T,
          mkConst cache.isSieveName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
          Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst packName])
    logInfo s!"run_harmonic_window {bound}: {len} positions in {wins.size} windows of {B}, \
segments of {G}, packed fold, sieve {cache.litName}; A = {T % P}, C = {T / P}"
    return
  let foldName := `PrimeCert ++ Name.mkSimple s!"harmonicWindowFold_{tag}"
  let aTot ← emitWindowFold foldName fRecip gRecip bRecip (·.recip) wins winNames len G
  if folds == 2 then
    let fCount := mkApp (mkConst ``bitAtK) sE
    let gCount : Nat → Nat → Expr := fun w _ ↦ mkApp (mkConst ``bitAtW) (mkRawNatLit w)
    let bCount : Nat → Nat → Nat → Name → Expr := fun lo n w nm ↦
      mkAppN (mkConst ``bit_window) #[sE, mkRawNatLit lo, mkRawNatLit n, mkRawNatLit w, mkConst nm]
    let countName := `PrimeCert ++ Name.mkSimple s!"harmonicWindowCount_{tag}"
    let cTot ← emitWindowFold countName fCount gCount bCount (·.count) wins winNames len G
    addHarmonicThm iccName
      (mkAppN (mkConst ``PrimeRecipIcc)
        #[mkRawNatLit bound, mkRawNatLit aTot, mkRawNatLit cTot, SE])
      (mkAppN (mkConst ``primeRecipIcc_of)
        (side ++ #[mkRawNatLit aTot, mkRawNatLit cTot, mkConst cache.isSieveName,
          Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
          Lean.reflBoolTrue, mkConst foldName, mkConst countName]))
    logInfo s!"run_harmonic_window {bound}: {len} positions in {wins.size} windows of {B}, \
segments of {G}, two folds, sieve {cache.litName}; A = {aTot}, C = {cTot}"
  else
    addHarmonicThm iccName
      (mkAppN (mkConst ``PrimeRecipIcc)
        #[mkRawNatLit bound, mkRawNatLit aTot, mkRawNatLit len, SE])
      (mkAppN (mkConst ``primeRecipIcc_of_single)
        (side ++ #[mkRawNatLit aTot, mkConst cache.isSieveName,
          Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
          Lean.reflBoolTrue, mkConst foldName]))
    logInfo s!"run_harmonic_window {bound}: {len} positions in {wins.size} windows of {B}, \
segments of {G}, one fold, sieve {cache.litName}; A = {aTot}, width {len} / S"

/-- `run_harmonic_window bound e B G folds` encloses the sum of the reciprocals of the primes up to
`bound` at scale `10 ^ e`, reading every batch of `B` positions through its own window of the sieve,
with the batches grouped into segments of `G` (`0` for one chain) and `folds` equal to `1`, `2`
or `3` (see `runHarmonicWindow`). -/
elab "run_harmonic_window" bStx:num eStx:num lStx:num gStx:num fStx:num : command =>
  liftTermElabM <|
    runHarmonicWindow bStx.getNat eStx.getNat lStx.getNat gStx.getNat fStx.getNat

end PrimeCert
