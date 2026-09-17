/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.PrimeHarmonic
public meta import PrimeCert.Meta.SieveCache
public meta import PrimeCert.SegmentedSieve

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

/-- One proved range: the positions `lo … lo + len - 1`, their total, and the declaration proving
`sumB fE lo len 1 = tot`. -/
structure RunNode where
  lo : Nat
  len : Nat
  tot : Nat
  name : Name

/-- The empty range, so that the elaborator can index arrays of ranges with `!`. -/
meta instance : Inhabited RunNode := ⟨⟨0, 0, 0, Name.anonymous⟩⟩

/-- Join adjacent proved ranges in a balanced tree, one `sumB_join` per declaration, and return the
range covering them all. The ranges must be consecutive, the first starting where the previous
ends. -/
meta def joinNodes (parent : Name) (fE : Expr) (nodes : Array RunNode) : MetaM RunNode := do
  if nodes.isEmpty then
    throwError "joinNodes: no ranges to join"
  let env ← getEnv
  let oneE := mkRawNatLit 1
  let mut cur := nodes
  let mut level := 0
  while cur.size > 1 do
    let mut next : Array RunNode := #[]
    let mut i := 0
    while i < cur.size do
      if i + 1 < cur.size then
        let x := cur[i]!
        let y := cur[i + 1]!
        let tot := x.len + y.len
        let t := x.tot + y.tot
        let nm := mkPrivateName env (parent ++ Name.mkSimple s!"node_{level}_{i}")
        addHarmonicThm nm
          (mkNatEq (mkAppN (mkConst ``sumB) #[fE, mkRawNatLit x.lo, mkRawNatLit tot, oneE])
            (mkRawNatLit t))
          (mkAppN (mkConst ``sumB_join)
            #[fE, mkRawNatLit x.lo, oneE, mkRawNatLit x.len, mkRawNatLit y.len, mkRawNatLit tot,
              mkRawNatLit y.lo, mkRawNatLit x.tot, mkRawNatLit y.tot, mkRawNatLit t,
              Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst x.name, mkConst y.name,
              Lean.reflBoolTrue])
        next := next.push { lo := x.lo, len := tot, tot := t, name := nm }
        i := i + 2
      else
        next := next.push cur[i]!
        i := i + 1
    cur := next
    level := level + 1
  return cur[0]!

/-- Which form of the batch statements the equations cite, set by the trailing argument of the
commands so that the forms can be timed against each other in one job. `0` is the statements with
ordinary numerals, `1` those whose numerals are raw literals, matching the terms the emitter builds,
and `2` those whose batch fold also drops the step to multiply by and the start to add. -/
meta def statementForm : IO.Ref Nat := unsafe unsafeBaseIO (IO.mkRef 2)

/-- Emit one equation per batch `a … b - 1` of one fold, each reading its own window, then join them
in a balanced tree, so that every declaration joins exactly two adjacent ranges. Returns the total
and a proof of `sumB fE lo n 1 = <total>`, where `lo` is the first position of batch `a` and `n` the
number of positions covered. `gE w lo` is the windowed fold function of a batch and
`bridge lo n w name` its bridge equation from the window theorem `name`. -/
meta def emitWindowRun (parent : Name) (fE : Expr) (gE : Nat → Nat → Expr)
    (bridge : Nat → Nat → Nat → Name → Expr) (pick : WindowBatch → Nat)
    (wins : Array WindowBatch) (winNames : Array Name) (a b : Nat) : MetaM (Nat × Expr) := do
  let form ← statementForm.get
  let env ← getEnv
  let oneE := mkRawNatLit 1
  let zeroE := mkRawNatLit 0
  let mut nodes : Array RunNode := #[]
  for k in [a:b] do
    let wb := wins[k]!
    let gw := gE wb.w wb.lo
    let t := pick wb
    -- the batch's own fold, step-free in form 2 and the unit-step fold from 0 otherwise
    let batchFold := if form == 2 then mkApp2 (mkConst ``sumB1) gw (mkRawNatLit wb.len)
      else mkAppN (mkConst ``sumB) #[gw, zeroE, mkRawNatLit wb.len, oneE]
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{k}")
    addHarmonicThm stepName
      (mkEqTrue (mkApp2 (mkConst ``Nat.beq) batchFold (mkRawNatLit t))) Lean.reflBoolTrue
    let hb := bridge wb.lo wb.len wb.w winNames[k]!
    let eqName := mkPrivateName env (parent ++ Name.mkSimple s!"eq_{k}")
    let eqLemma := match form with
      | 0 => ``sumB_windowEq
      | 1 => ``sumB_windowEqR
      | _ => ``sumB_windowEq1
    addHarmonicThm eqName
      (mkNatEq (mkAppN (mkConst ``sumB) #[fE, mkRawNatLit wb.lo, mkRawNatLit wb.len, oneE])
        (mkRawNatLit t))
      (mkAppN (mkConst eqLemma)
        #[fE, gw, mkRawNatLit wb.lo, mkRawNatLit wb.len, mkRawNatLit t, hb, mkConst stepName])
    nodes := nodes.push { lo := wb.lo, len := wb.len, tot := t, name := eqName }
  let root ← joinNodes parent fE nodes
  return (root.tot, mkConst root.name)

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
        mkAppN (mkConst ``sumB_lastEqL)
          #[fE, lhs, mkRawNatLit segLo, oneE, mkRawNatLit segLen, mkRawNatLit owed, accE,
            mkRawNatLit segTot, mkRawNatLit next, proof, Lean.reflBoolTrue, mkConst segName,
            Lean.reflBoolTrue]
      else
        mkAppN (mkConst ``sumB_chainEqL)
          #[fE, lhs, mkRawNatLit segLo, oneE, mkRawNatLit segLen, mkRawNatLit (owed - segLen),
            mkRawNatLit owed, mkRawNatLit (segLo + segLen), accE, mkRawNatLit segTot,
            mkRawNatLit next, proof, Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst segName,
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
  let form ← statementForm.get
  let bRecip : Nat → Nat → Nat → Name → Expr := fun lo n w nm ↦
    mkAppN (mkConst (match form with
        | 0 => ``recip_window
        | 1 => ``recip_windowR
        | _ => ``recip_window1))
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
      mkAppN (mkConst (match form with
          | 0 => ``pack_window
          | 1 => ``pack_windowR
          | _ => ``pack_window1))
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
      mkAppN (mkConst (if form == 0 then ``bit_window else ``bit_windowR))
        #[sE, mkRawNatLit lo, mkRawNatLit n, mkRawNatLit w, mkConst nm]
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
or `3` (see `runHarmonicWindow`). The trailing numeral picks the form of the batch statements, `0`
ordinary numerals, `1` raw literals, `2` raw literals and a step-free batch fold, for timing the
three against each other; it defaults to `2`. -/
elab "run_harmonic_window" bStx:num eStx:num lStx:num gStx:num fStx:num rStx:(num)? : command =>
  liftTermElabM <| do
    statementForm.set (match rStx with | none => 2 | some r => r.getNat)
    runHarmonicWindow bStx.getNat eStx.getNat lStx.getNat gStx.getNat fStx.getNat
    statementForm.set 2

/-! ## Runs of positions that share a quotient

High up the sieve the truncated quotient `S / value t` is the same for many positions in a row, and
such a run needs only the count of its set bits: its contribution is the quotient times that count
(`sumB_recipAtK_const_ends`). Below the crossover the quotient changes too often for that to pay,
and the positions are summed one by one as before. -/

/-- The last position at or below `hi` whose value still has quotient `q`, for `q ≠ 0`. -/
meta def quotientRunEnd (S q hi : Nat) : Nat := Id.run do
  let vmax := S / q
  let mut t := twinIndex vmax
  for _ in [0:3] do
    if twinValue t > vmax then
      t := t - 1
  for _ in [0:3] do
    if twinValue (t + 1) ≤ vmax then
      t := t + 1
  return Nat.min hi t

/-- The maximal runs of constant quotient covering the positions `lo … hi`, each as its first
position, its length and the quotient its positions share. -/
meta def quotientRuns (S lo hi : Nat) : Array (Nat × Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat × Nat) := #[]
  let mut p := lo
  while p ≤ hi do
    let q := S / twinValue p
    let e := Nat.max p (if q == 0 then hi else quotientRunEnd S q hi)
    out := out.push (p, e - p + 1, q)
    p := e + 1
  return out

/-- The batches of `B` consecutive positions covering `lo … lo + n - 1`, with their windows and
totals. `twinWindows` is this with `lo = 1` and `n` the whole run. -/
meta def twinWindowsRange (mark : ByteArray) (S lo n B : Nat) : Array WindowBatch := Id.run do
  let mut out : Array WindowBatch := #[]
  for i in [0:(n + B - 1) / B] do
    let a := lo + i * B
    let m := Nat.min B (n - i * B)
    let mut r := 0
    let mut c := 0
    for j in [0:m] do
      if mark.get! (a + j) == 1 then
        r := r + S / twinValue (a + j)
        c := c + 1
    out := out.push { lo := a, len := m, w := twinWindow mark a m, recip := r, count := c }
  return out

/-! ## A windowed run split across files

`run_harmonic_window` proves everything in one command, so one file and one core do all the kernel
work. `run_harmonic_part` proves one share of the batches and `run_harmonic_merge` joins the shares,
so the shares can be separate modules that the build runs at the same time.
-/

/-- The sieve literal, its `IsSieve` theorem and the top it covers, the number of wheel positions
inside `bound`, and the batches of `B` positions with their windows. `cmd` names the caller in the
error messages. -/
meta def windowSetup (cmd : String) (bound scaleExp B : Nat) :
    MetaM (Nat × Name × Name × Nat × Array WindowBatch) := do
  if bound < 5 then
    throwError "{cmd}: the bound must be at least 5"
  let B := Nat.max 1 B
  let some cache ← Sieve.findSieveCache bound
    | throwError "{cmd}: no sieve cache in scope covers {bound}"
  let mut len := twinIndex bound
  for _ in [0:2] do
    if twinValue len > bound then
      len := len - 1
  if len == 0 || twinValue len > bound || twinValue (len + 1) ≤ bound then
    throwError "{cmd}: could not place the last wheel position inside {bound}"
  let wins := twinWindows (wheelMarks len) (10 ^ scaleExp) len B
  return (cache.hi, cache.litName, cache.isSieveName, len, wins)

/-- The packed fold over the sieve `sE` at scale `S` with packing base `P`: the kernel function, the
windowed function of a batch, the bridge from a batch's window theorem, and the batch total. -/
meta def packPieces (sE : Expr) (S P : Nat) :
    Expr × (Nat → Nat → Expr) × (Nat → Nat → Nat → Name → Expr) × (WindowBatch → Nat) :=
  let SE := mkRawNatLit S
  let PE := mkRawNatLit P
  (mkApp3 (mkConst ``packAtK) sE SE PE,
    fun w lo ↦ mkApp4 (mkConst ``packAtW) (mkRawNatLit w) (mkRawNatLit lo) SE PE,
    fun lo n w nm ↦ mkAppN (mkConst ``pack_window)
      #[sE, SE, PE, mkRawNatLit lo, mkRawNatLit n, mkRawNatLit w, mkConst nm],
    fun wb ↦ wb.recip + P * wb.count)

/-- The batches of part `i` of `M`, as a half-open range of batch indices. -/
meta def partRange (nb M i : Nat) : Nat × Nat := (nb * i / M, nb * (i + 1) / M)

/-- The theorem part `i` of `M` proves, for the run `bound`, `scaleExp`, `B`. -/
meta def partName (bound scaleExp B M i : Nat) : Name :=
  `PrimeCert ++ Name.mkSimple s!"harmonicWindowPart_{bound}_{scaleExp}_{B}_{M}_{i}"

/-- Prove part `i` of `M` of the packed windowed run: the batches `partRange` gives it, each reading
its own window, joined in a tree into `partName …  : sumB packAtK … lo n 1 = <total>`. -/
meta def runHarmonicPart (bound scaleExp B M i : Nat) : MetaM Unit := do
  if M == 0 || i ≥ M then
    throwError "run_harmonic_part: {i} is not one of {M} parts"
  let (_, litName, _, len, wins) ← windowSetup "run_harmonic_part" bound scaleExp B
  let (a, b) := partRange wins.size M i
  if a == b then
    throwError "run_harmonic_part: part {i} of {M} has no batches"
  let sE := mkConst litName
  let (fE, gE, bridge, pick) := packPieces sE (10 ^ scaleExp) (len * 10 ^ scaleExp + 1)
  let nm := partName bound scaleExp B M i
  let env ← getEnv
  let mut winNames : Array Name := #[]
  for _ in [0:a] do
    winNames := winNames.push Name.anonymous
  for k in [a:b] do
    let wb := wins[k]!
    let wn := mkPrivateName env (nm ++ Name.mkSimple s!"w_{k}")
    addHarmonicThm wn (mkWindowEq sE wb.lo wb.len wb.w) Lean.reflBoolTrue
    winNames := winNames.push wn
  let (tot, proof) ← emitWindowRun nm fE gE bridge pick wins winNames a b
  addHarmonicThm nm (mkNatEq (mkSumB fE wins[a]!.lo (windowSpan wins a b) 1) (mkRawNatLit tot))
    proof
  logInfo s!"run_harmonic_part {bound}: part {i} of {M} is batches {a} to {b - 1}, \
{windowSpan wins a b} positions from {wins[a]!.lo}, total {tot}"

/-- Join the `M` parts of the packed windowed run in a tree and land
`primeRecipIccWindow_… : PrimeRecipIcc bound A C (10 ^ scaleExp)`. The parts must be in scope, each
proved by `run_harmonic_part` with the same `bound`, `scaleExp`, `B` and `M`. -/
meta def runHarmonicMerge (bound scaleExp B M : Nat) : MetaM Unit := do
  if M == 0 then
    throwError "run_harmonic_merge: there must be at least one part"
  let (hi, litName, isSieveName, len, wins) ← windowSetup "run_harmonic_merge" bound scaleExp B
  let S := 10 ^ scaleExp
  let P := len * S + 1
  let sE := mkConst litName
  let (fE, _, _, pick) := packPieces sE S P
  let mut nodes : Array RunNode := #[]
  for i in [0:M] do
    let (a, b) := partRange wins.size M i
    if a == b then
      throwError "run_harmonic_merge: part {i} of {M} has no batches"
    let mut t := 0
    for k in [a:b] do
      t := t + pick wins[k]!
    nodes := nodes.push
      { lo := wins[a]!.lo, len := windowSpan wins a b, tot := t,
        name := partName bound scaleExp B M i }
  let tag := s!"{bound}_{scaleExp}_{B}_{M}"
  let root ← joinNodes (`PrimeCert ++ Name.mkSimple s!"harmonicWindowMerge_{tag}") fE nodes
  let T := root.tot
  let iccName := `PrimeCert ++ Name.mkSimple s!"primeRecipIccWindow_{tag}"
  addHarmonicThm iccName
    (mkAppN (mkConst ``PrimeRecipIcc)
      #[mkRawNatLit bound, mkRawNatLit (T % P), mkRawNatLit (T / P), mkRawNatLit S])
    (mkAppN (mkConst ``primeRecipIcc_of_pack)
      #[mkRawNatLit hi, mkRawNatLit bound, mkRawNatLit S, mkRawNatLit P, sE, mkRawNatLit len,
        mkRawNatLit T, mkConst isSieveName, Lean.reflBoolTrue, Lean.reflBoolTrue,
        Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
        mkConst root.name])
  logInfo s!"run_harmonic_merge {bound}: {len} positions in {wins.size} windows of {B} across \
{M} parts, sieve {litName}; A = {T % P}, C = {T / P}"

/-- Emit the window certificates for `batches` and fold them into one equation
`sumB fE lo n 1 = <total>`, returning the total and the name of that equation. -/
meta def emitWindowedFoldOver (parent : Name) (fE : Expr) (gE : Nat → Nat → Expr)
    (bridge : Nat → Nat → Nat → Name → Expr) (pick : WindowBatch → Nat)
    (batches : Array WindowBatch) (winNames : Array Name) : MetaM (Nat × Name) := do
  let (tot, proof) ← emitWindowRun parent fE gE bridge pick batches winNames 0 batches.size
  let lo := batches[0]!.lo
  let n := windowSpan batches 0 batches.size
  addHarmonicThm parent (mkNatEq (mkSumB fE lo n 1) (mkRawNatLit tot)) proof
  return (tot, parent)

/-- Enclose `∑ p ≤ bound, 1/p` at scale `10 ^ scaleExp`, summing the positions below `split` one at
a time and the positions from `split` up in runs that share a quotient, each such run costing one
count of set bits. `B` is the number of positions a window covers. -/
meta def runHarmonicCoarse (bound scaleExp B split : Nat) : MetaM Unit := do
  let (hi, litName, isSieveName, len, _) ← windowSetup "run_harmonic_coarse" bound scaleExp B
  let B := Nat.max 1 B
  let split := Nat.max 2 (Nat.min split (len + 1))
  let S := 10 ^ scaleExp
  let sE := mkConst litName
  let SE := mkRawNatLit S
  let mark := wheelMarks len
  let fRecip := mkApp2 (mkConst ``recipAtK) sE SE
  let gRecip : Nat → Nat → Expr := fun w lo ↦
    mkApp3 (mkConst ``recipAtW) (mkRawNatLit w) (mkRawNatLit lo) SE
  let bRecip : Nat → Nat → Nat → Name → Expr := fun lo n w nm ↦
    mkAppN (mkConst ``recip_windowR)
      #[sE, SE, mkRawNatLit lo, mkRawNatLit n, mkRawNatLit w, mkConst nm]
  let fCount := mkApp (mkConst ``bitAtK) sE
  let gCount : Nat → Nat → Expr := fun w _ ↦ mkApp (mkConst ``bitAtW) (mkRawNatLit w)
  let bCount : Nat → Nat → Nat → Name → Expr := fun lo n w nm ↦
    mkAppN (mkConst ``bit_windowR) #[sE, mkRawNatLit lo, mkRawNatLit n, mkRawNatLit w, mkConst nm]
  let tag := s!"{bound}_{scaleExp}_{B}_{split}"
  let base := `PrimeCert ++ Name.mkSimple s!"harmonicCoarse_{tag}"
  let env ← getEnv
  let mut recipNodes : Array RunNode := #[]
  let mut countNodes : Array RunNode := #[]
  -- the positions below the crossover, summed one at a time
  if split > 1 then
    let fine := twinWindowsRange mark S 1 (split - 1) B
    let mut winNames : Array Name := #[]
    for k in [0:fine.size] do
      let wb := fine[k]!
      let nm := mkPrivateName env (base ++ Name.mkSimple s!"fw_{k}")
      addHarmonicThm nm (mkWindowEq sE wb.lo wb.len wb.w) Lean.reflBoolTrue
      winNames := winNames.push nm
    let (aTot, aName) ← emitWindowedFoldOver (base ++ Name.mkSimple "fineRecip") fRecip
      gRecip bRecip (·.recip) fine winNames
    let (cTot, cName) ← emitWindowedFoldOver (base ++ Name.mkSimple "fineCount") fCount
      gCount bCount (·.count) fine winNames
    recipNodes := recipNodes.push { lo := 1, len := split - 1, tot := aTot, name := aName }
    countNodes := countNodes.push { lo := 1, len := split - 1, tot := cTot, name := cName }
  -- the positions above it, one count per run of equal quotient
  let runs := quotientRuns S split len
  for r in [0:runs.size] do
    let (lo, n, q) := runs[r]!
    let batches := twinWindowsRange mark S lo n B
    let mut winNames : Array Name := #[]
    for k in [0:batches.size] do
      let wb := batches[k]!
      let nm := mkPrivateName env (base ++ Name.mkSimple s!"cw_{r}_{k}")
      addHarmonicThm nm (mkWindowEq sE wb.lo wb.len wb.w) Lean.reflBoolTrue
      winNames := winNames.push nm
    let (c, cName) ← emitWindowedFoldOver (base ++ Name.mkSimple s!"runCount_{r}") fCount
      gCount bCount (·.count) batches winNames
    let aName := base ++ Name.mkSimple s!"runRecip_{r}"
    addHarmonicThm aName (mkNatEq (mkSumB fRecip lo n 1) (mkRawNatLit (q * c)))
      (mkAppN (mkConst ``sumB_recipAtK_const_ends)
        #[sE, SE, mkRawNatLit q, mkRawNatLit lo, mkRawNatLit n, mkRawNatLit c,
          mkRawNatLit (q * c), Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst cName,
          Lean.reflBoolTrue])
    recipNodes := recipNodes.push { lo, len := n, tot := q * c, name := aName }
    countNodes := countNodes.push { lo, len := n, tot := c, name := cName }
  let aRoot ← joinNodes (base ++ Name.mkSimple "recip") fRecip recipNodes
  let cRoot ← joinNodes (base ++ Name.mkSimple "count") fCount countNodes
  let iccName := `PrimeCert ++ Name.mkSimple s!"primeRecipIccCoarse_{tag}"
  addHarmonicThm iccName
    (mkAppN (mkConst ``PrimeRecipIcc)
      #[mkRawNatLit bound, mkRawNatLit aRoot.tot, mkRawNatLit cRoot.tot, SE])
    (mkAppN (mkConst ``primeRecipIcc_of)
      #[mkRawNatLit hi, mkRawNatLit bound, SE, sE, mkRawNatLit len, mkRawNatLit aRoot.tot,
        mkRawNatLit cRoot.tot, mkConst isSieveName, Lean.reflBoolTrue, Lean.reflBoolTrue,
        Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst aRoot.name,
        mkConst cRoot.name])
  logInfo s!"run_harmonic_coarse {bound}: {len} positions, one at a time below {split} \
({twinValue split}), then {runs.size} runs of equal quotient, windows of {B}, \
sieve {litName}; A = {aRoot.tot}, C = {cRoot.tot}"

/-- `run_harmonic_coarse bound e B split` encloses the sum with the positions below `split` summed
one at a time and the rest in runs of equal quotient (see `runHarmonicCoarse`). -/
elab "run_harmonic_coarse" bStx:num eStx:num lStx:num sStx:num : command =>
  liftTermElabM <|
    runHarmonicCoarse bStx.getNat eStx.getNat lStx.getNat sStx.getNat

/-! ## One segment above the base sieve

`run_harmonic_segment` sieves one window of numbers above the base sieve with the other session's
`run_segment`, then sums it exactly as the base range is summed: batches of `B` positions, each
reading its own window of the segment literal, joined in a tree. It lands
`PrimeRecipRange a top A C S`, the enclosure of the sum over the primes of that window, which
`primeRecipRange_add` joins to its neighbours. -/

/-- The proof term `Or.inl rfl` or `Or.inr rfl` for `a % 6 = 1 ∨ a % 6 = 5`. -/
meta def mkMod6Proof (a r : Nat) : Expr :=
  let refl := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[Nat.mkType, mkRawNatLit r]
  let lhs := mkNatEq (mkApp2 (mkConst ``Nat.mod) (mkRawNatLit a) (mkRawNatLit 6)) (mkRawNatLit 1)
  let rhs := mkNatEq (mkApp2 (mkConst ``Nat.mod) (mkRawNatLit a) (mkRawNatLit 6)) (mkRawNatLit 5)
  if r == 1 then mkApp3 (mkConst ``Or.inl) lhs rhs refl
  else mkApp3 (mkConst ``Or.inr) lhs rhs refl

/-- Sum the window of `W` wheel positions from `a`, already sieved by `run_segment a W fuel len B`
in the same namespace, at scale `10 ^ scaleExp` in batches of `batch` positions, and enclose the sum
over its primes. `len` must match the one given to `run_segment`, since it names the segment. -/
meta def runHarmonicSegment (a W B scaleExp batch len : Nat) : MetaM Unit := do
  let r := a % 6
  if r != 1 && r != 5 then
    throwError "run_harmonic_segment: the window start {a} is not 1 or 5 modulo 6"
  let rB := B % 6
  if rB != 1 && rB != 5 then
    throwError "run_harmonic_segment: the bound {B} is not 1 or 5 modulo 6"
  if 7 * B > a then
    throwError "run_harmonic_segment: the window must start at or above {7 * B}"
  if W == 0 then
    throwError "run_harmonic_segment: the window is empty"
  let fuel := twinIndex B
  if twinValue fuel != B then
    throwError "run_harmonic_segment: {B} is not a wheel value"
  let some cache ← Sieve.findSieveCache B
    | throwError "run_harmonic_segment: no sieve cache in scope covers {B}"
  if cache.hi < B then
    throwError "run_harmonic_segment: the sieve in scope stops at {cache.hi}, below {B}"
  let lo := twinIndex a
  if twinValue lo != a then
    throwError "run_harmonic_segment: {a} is not a wheel value"
  let top := twinValue (lo + W - 1)
  let next := twinValue (lo + W)
  if top ≥ B * B then
    throwError "run_harmonic_segment: the window reaches {top}, at or above {B * B}"
  let batch := Nat.max 1 batch
  let S := 10 ^ scaleExp
  let ns ← getCurrNamespace
  let tag := s!"{a}_{W}_{fuel}_{Nat.max 1 len}"
  let segLit := ns ++ Name.mkSimple s!"segBits_{tag}"
  let segEqI := ns ++ Name.mkSimple s!"segEqI_{tag}"
  let env ← getEnv
  let some info := env.find? segLit
    | throwError "run_harmonic_segment: no segment {segLit}; run \
`run_segment {a} {W} {fuel} {len} {B}` above this command"
  let some g := info.value?.bind Expr.rawNatLit?
    | throwError "run_harmonic_segment: the segment {segLit} is not a numeral"
  let gE := mkConst segLit
  let SE := mkRawNatLit S
  let loE := mkRawNatLit lo
  -- the batches of the segment, with their windows and totals read off the segment literal
  let mut wins : Array WindowBatch := #[]
  for i in [0:(W + batch - 1) / batch] do
    let k := i * batch
    let m := Nat.min batch (W - k)
    let mut w := 0
    let mut tot := 0
    let mut cnt := 0
    for j in [0:m] do
      if g.testBit (k + m - 1 - j) then
        w := 2 * w + 1
      else
        w := 2 * w
      if g.testBit (k + j) then
        tot := tot + S / twinValue (lo + k + j)
        cnt := cnt + 1
    wins := wins.push { lo := k, len := m, w, recip := tot, count := cnt }
  let base := `PrimeCert ++ Name.mkSimple s!"harmonicSegment_{a}_{W}_{B}_{scaleExp}_{batch}"
  let mut winNames : Array Name := #[]
  for k in [0:wins.size] do
    let wb := wins[k]!
    let nm := mkPrivateName env (base ++ Name.mkSimple s!"w_{k}")
    addHarmonicThm nm (mkWindowEq gE wb.lo wb.len wb.w) Lean.reflBoolTrue
    winNames := winNames.push nm
  let fRecip := mkApp3 (mkConst ``recipAtW) gE loE SE
  let gRecip : Nat → Nat → Expr := fun w k ↦
    mkApp3 (mkConst ``recipAtW) (mkRawNatLit w) (mkRawNatLit (lo + k)) SE
  let bRecip : Nat → Nat → Nat → Name → Expr := fun k n w nm ↦
    mkAppN (mkConst ``recipW_windowR)
      #[gE, SE, loE, mkRawNatLit k, mkRawNatLit (lo + k), mkRawNatLit n, mkRawNatLit w,
        Lean.reflBoolTrue, mkConst nm]
  let fCount := mkApp (mkConst ``bitAtW) gE
  let gCount : Nat → Nat → Expr := fun w _ ↦ mkApp (mkConst ``bitAtW) (mkRawNatLit w)
  let bCount : Nat → Nat → Nat → Name → Expr := fun k n w nm ↦
    mkAppN (mkConst ``bitW_windowR)
      #[gE, mkRawNatLit k, mkRawNatLit n, mkRawNatLit w, mkConst nm]
  let (A, aName) ← emitWindowedFoldOver (base ++ Name.mkSimple "recip") fRecip
    gRecip bRecip (·.recip) wins winNames
  let (C, cName) ← emitWindowedFoldOver (base ++ Name.mkSimple "count") fCount
    gCount bCount (·.count) wins winNames
  let iccName := `PrimeCert ++ Name.mkSimple s!"primeRecipRange_{a}_{W}_{B}_{scaleExp}"
  addHarmonicThm iccName
    (mkAppN (mkConst ``PrimeRecipRange)
      #[mkRawNatLit a, mkRawNatLit next, mkRawNatLit A, mkRawNatLit C, SE])
    (mkAppN (mkConst ``primeRecipRange_of_segRun)
      #[mkConst cache.litName, mkRawNatLit B, mkRawNatLit a, mkRawNatLit W, SE, gE,
        mkRawNatLit A, mkRawNatLit C, loE, mkRawNatLit next,
        mkAppN (mkConst ``Sieve.IsSieve.monoB)
          #[mkRawNatLit cache.hi, mkRawNatLit B, mkConst cache.litName,
            mkConst cache.isSieveName, Lean.reflBoolTrue],
        mkMod6Proof a r, mkMod6Proof B rB, Lean.reflBoolTrue, Lean.reflBoolTrue,
        Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
        Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst segEqI,
        mkConst aName, mkConst cName])
  logInfo s!"run_harmonic_segment {a}: {W} positions up to {top}, {wins.size} windows of {batch}, \
divisors to {B}; A = {A}, C = {C}"

/-- The start of the window after the one of `W` positions from `a`. -/
meta def nextSegmentStart (a W : Nat) : Nat := twinValue (twinIndex a + W)

/-- The name `run_harmonic_segment` gives the enclosure of the window of `W` positions from `a`. -/
meta def segmentRangeName (a W B scaleExp : Nat) : Name :=
  `PrimeCert ++ Name.mkSimple s!"primeRecipRange_{a}_{W}_{B}_{scaleExp}"

/-- One proved range of primes: its first number, the number after its last, its two totals, and
the declaration proving the enclosure. -/
structure RangeNode where
  lo : Nat
  hi : Nat
  tot : Nat
  cnt : Nat
  name : Name

/-- The empty range, so that the elaborator can index arrays of ranges with `!`. -/
meta instance : Inhabited RangeNode := ⟨⟨0, 0, 0, 0, Name.anonymous⟩⟩

/-- Join `n` neighbouring enclosures in a balanced tree, one addition per declaration. -/
meta def joinRanges (parent : Name) (SE : Expr) (nodes : Array RangeNode) : MetaM RangeNode := do
  if nodes.isEmpty then
    throwError "joinRanges: no ranges to join"
  let env ← getEnv
  let mut cur := nodes
  let mut level := 0
  while cur.size > 1 do
    let mut next : Array RangeNode := #[]
    let mut i := 0
    while i < cur.size do
      if i + 1 < cur.size then
        let x := cur[i]!
        let y := cur[i + 1]!
        if x.hi != y.lo then
          throwError "joinRanges: {x.hi} and {y.lo} are not neighbours"
        let tot := x.tot + y.tot
        let cnt := x.cnt + y.cnt
        let nm := mkPrivateName env (parent ++ Name.mkSimple s!"node_{level}_{i}")
        addHarmonicThm nm
          (mkAppN (mkConst ``PrimeRecipRange)
            #[mkRawNatLit x.lo, mkRawNatLit y.hi, mkRawNatLit tot, mkRawNatLit cnt, SE])
          (mkAppN (mkConst ``primeRecipRange_add)
            #[mkRawNatLit x.lo, mkRawNatLit x.hi, mkRawNatLit y.hi, mkRawNatLit x.tot,
              mkRawNatLit x.cnt, mkRawNatLit y.tot, mkRawNatLit y.cnt, mkRawNatLit tot,
              mkRawNatLit cnt, SE, Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst x.name,
              mkConst y.name, Lean.reflBoolTrue, Lean.reflBoolTrue])
        next := next.push { lo := x.lo, hi := y.hi, tot, cnt, name := nm }
        i := i + 2
      else
        next := next.push cur[i]!
        i := i + 1
    cur := next
    level := level + 1
  return cur[0]!

/-- Join the `n` windows of `W` positions from `a`, each already summed by
`run_harmonic_segment`, into one enclosure of the sum over the primes they cover. -/
meta def runHarmonicJoin (a W B scaleExp n : Nat) : MetaM Unit := do
  if n == 0 then
    throwError "run_harmonic_join: there are no windows to join"
  let env ← getEnv
  let SE := mkRawNatLit (10 ^ scaleExp)
  let mut nodes : Array RangeNode := #[]
  let mut start := a
  for _ in [0:n] do
    let nm := segmentRangeName start W B scaleExp
    let some info := env.find? nm
      | throwError "run_harmonic_join: no enclosure {nm}; \
run `run_harmonic_segment {start} {W} {B} {scaleExp} …` above this command"
    let some args := info.type.getAppArgs[0:5] |>.toArray.mapM Expr.rawNatLit?
      | throwError "run_harmonic_join: the enclosure {nm} does not carry five numerals"
    nodes := nodes.push
      { lo := args[0]!, hi := args[1]!, tot := args[2]!, cnt := args[3]!, name := nm }
    start := nextSegmentStart start W
  let base := `PrimeCert ++ Name.mkSimple s!"harmonicJoin_{a}_{W}_{B}_{scaleExp}_{n}"
  let root ← joinRanges base SE nodes
  let nm := `PrimeCert ++ Name.mkSimple s!"primeRecipRange_{a}_{root.hi}_{scaleExp}"
  addHarmonicThm nm
    (mkAppN (mkConst ``PrimeRecipRange)
      #[mkRawNatLit root.lo, mkRawNatLit root.hi, mkRawNatLit root.tot, mkRawNatLit root.cnt, SE])
    (mkConst root.name)
  logInfo s!"run_harmonic_join: {n} windows cover {root.lo} to {root.hi - 1}; \
A = {root.tot}, C = {root.cnt}"

/-- Sieve, sum and join `n` neighbouring windows of `W` positions from `a` in one command: the
sieving of each window is emitted here rather than written out by hand, so a long stretch of numbers
above the base sieve is one line. -/
meta def runHarmonicSeries (a W B scaleExp batch len n : Nat) : MetaM Unit := do
  if n == 0 then
    throwError "run_harmonic_series: there are no windows to sum"
  let fuel := twinIndex B
  if twinValue fuel != B then
    throwError "run_harmonic_series: {B} is not a wheel value"
  let some cache ← Sieve.findSieveCache B
    | throwError "run_harmonic_series: no sieve cache in scope covers {B}"
  let ns ← getCurrNamespace
  let mut start := a
  for _ in [0:n] do
    Sieve.runSegment ns cache.litName start W fuel len
    runHarmonicSegment start W B scaleExp batch len
    start := nextSegmentStart start W
  runHarmonicJoin a W B scaleExp n

/-- `run_harmonic_series a W B e batch len n` sieves, sums and joins `n` neighbouring windows of
`W` positions from `a` (see `runHarmonicSeries`). As for `run_harmonic_window`, a trailing numeral
picks the form of the batch statements and defaults to `2`. -/
elab "run_harmonic_series" aStx:num wStx:num bStx:num eStx:num cStx:num lStx:num nStx:num
    rStx:(num)? : command =>
  liftTermElabM <| do
    statementForm.set (match rStx with | none => 2 | some r => r.getNat)
    runHarmonicSeries aStx.getNat wStx.getNat bStx.getNat eStx.getNat cStx.getNat
      lStx.getNat nStx.getNat
    statementForm.set 2

/-- `run_harmonic_join a W B e n` joins the `n` windows of `W` positions from `a` (see
`runHarmonicJoin`). -/
elab "run_harmonic_join" aStx:num wStx:num bStx:num eStx:num nStx:num : command =>
  liftTermElabM <|
    runHarmonicJoin aStx.getNat wStx.getNat bStx.getNat eStx.getNat nStx.getNat

/-- `run_harmonic_segment a W B e batch len` sieves the window of `W` wheel positions from `a` by
the primes up to `B` and encloses the sum of the reciprocals of its primes at scale `10 ^ e` (see
`runHarmonicSegment`). -/
elab "run_harmonic_segment" aStx:num wStx:num bStx:num eStx:num cStx:num lStx:num : command =>
  liftTermElabM <|
    runHarmonicSegment aStx.getNat wStx.getNat bStx.getNat eStx.getNat cStx.getNat lStx.getNat

/-- `run_harmonic_part bound e B M i` proves part `i` of `M` of the packed windowed run for
`∑ p ≤ bound, 1/p` at scale `10 ^ e` with batches of `B` positions (see `runHarmonicPart`). -/
elab "run_harmonic_part" bStx:num eStx:num lStx:num mStx:num iStx:num : command =>
  liftTermElabM <|
    runHarmonicPart bStx.getNat eStx.getNat lStx.getNat mStx.getNat iStx.getNat

/-- `run_harmonic_merge bound e B M` joins the `M` parts of that run and encloses the sum (see
`runHarmonicMerge`). -/
elab "run_harmonic_merge" bStx:num eStx:num lStx:num mStx:num : command =>
  liftTermElabM <| runHarmonicMerge bStx.getNat eStx.getNat lStx.getNat mStx.getNat

end PrimeCert
