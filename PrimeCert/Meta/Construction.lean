/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public meta import PrimeCert.Construction
public meta import PrimeCert.Meta.Pocklington3
public meta import PrimeCert.Meta.SieveLookup
public import Lean.Meta.Tactic.TryThis

/-! Opt-in certificate construction with a reusable literal ladder suggestion. -/
public meta section
namespace PrimeCert.Meta
open Lean Meta Elab Tactic

/-- Enumerate the existing certified sieve, including its exceptional primes. No new sieve or
large generated proof is needed. The cache must cover the full requested smoothness bound. -/
def constructionPrimes (bound : Nat) : MetaM (Array Nat) := do
  if bound < 5 then return #[2, 3].filter (· ≤ bound)
  let some cache ← Sieve.findSieveCache bound
    | throwError "prime_cert?: no certified sieve covers the construction bound {bound}"
  unless cache.lo ≤ 5 do
    throwError "prime_cert?: construction requires a sieve starting at 5 or below"
  let some bits := (← getEnv).find? cache.litName >>= (·.value?) >>= (·.rawNatLit?)
    | throwError "prime_cert?: invalid sieve cache"
  let mut result := #[]
  if 2 ≤ bound then result := result.push 2
  if 3 ≤ bound then result := result.push 3
  -- Each word is extracted once; reading every bit with a whole-Nat right shift
  -- would repeatedly copy most of the million-bit cache.
  for word in [:Sieve.index bound / 64 + 1] do
    let chunk := (bits >>> (64 * word)) &&& 18446744073709551615
    for bit in [:64] do
      let i := 64 * word + bit
      let q := Sieve.value i
      if i != 0 && q ≤ bound && chunk.testBit bit then result := result.push q
  return result

private def factorSource (fs : List (Nat × Nat)) : String :=
  String.intercalate " * " (fs.map fun (q, e) =>
    if e == 1 then toString q else s!"{q} ^ {e}")

/-- Serialize only dependencies of the requested root, in the existing ladder syntax.
This is shared by proof elaboration and `TryThis`; there is no second certificate encoder. -/
def constructionSource (n : Nat) (state : Construction.State) : String := Id.run do
  let mut needed := [n]
  for node in state.nodes.toList.reverse do
    if needed.contains node.n then
      needed := node.factors.map Prod.fst ++ needed
  let leaves := state.leaves.toList.filter needed.contains |>.mergeSort (· ≤ ·)
  let mut groups := if leaves.isEmpty then [] else
    ["sieve {" ++ String.intercalate "; " (leaves.map toString) ++ "}"]
  for node in state.nodes do
    if !needed.contains node.n then continue
    let factors := factorSource node.factors
    let group := match node.mode with
      | .pock => s!"pock ({node.n}, {node.root}, {factors})"
      | mode =>
        let mode := match mode with
          | .zero => "0" | .lt => "<" | .interval w => s!"interval {w}" | .pock => "0"
        if node.sieveBound == 1 then
          s!"pock3 ({node.n}, {node.root}, {mode}, {factors})"
        else s!"pock3 ({node.n}, {node.root}, {node.sieveBound}, {mode}, {factors})"
    groups := groups ++ [group]
  return "exact prime_cert%\n  [" ++ String.intercalate ",\n   " groups ++ "]"

public syntax constructionConfig := "(" &"config" ":=" term ")"

/-- Build a certificate with the explicit finite construction profile, close the goal using
kernel checking, and suggest the literal ladder so subsequent builds need no search.
An optional term supplies a `PrimeCert.Construction.Budget`. -/
elab "prime_cert?" config:(constructionConfig)? : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let_expr Nat.Prime arg := target
    | throwError "prime_cert?: expected a goal of the form `Nat.Prime _`"
  unless !arg.hasFVar && !arg.hasMVar do
    throwError "prime_cert?: expected a closed natural number"
  let budget ← match config with
    | none => pure ({} : Construction.Budget)
    | some cfg => do
      let e ← Tactic.elabTermEnsuringType cfg.raw[3] (mkConst ``Construction.Budget)
      unsafe evalExpr Construction.Budget (mkConst ``Construction.Budget) e
  let n ← unsafe evalExpr Nat (mkConst ``Nat) arg
  if n.log2 + 1 > budget.maxBits then
    throwError "prime_cert?: construction input exceeds {budget.maxBits} bits"
  let bound := budget.smoothBounds.foldl max (max 31 budget.trialBound)
  let primes ← constructionPrimes bound
  let (success, state) := Construction.run budget primes n
  unless success do
    throwError "prime_cert?: construction exhausted after {state.attempts} attempts \
      (limit {budget.maxAttempts}, depth {budget.maxDepth}, seed {state.seed.toNat})"
  let source := constructionSource n state
  let suggestion ← ofExcept <| Parser.runParserCategory (← getEnv) `tactic source
  -- Elaborate the exact source we will offer, then independently check its proof
  -- against the original target. Producer data and formatting are not trusted.
  withoutRecover (evalTactic suggestion)
  let proof ← instantiateMVars (mkMVar goal)
  if proof.hasSorry || proof.hasMVar then
    throwError "prime_cert?: generated certificate did not produce a complete proof"
  let checked := mkApp (mkLambda `h .default target (mkBVar 0)) proof
  let _ ← ofExceptKernelException <| Kernel.check (← getEnv) {} checked
  TryThis.addSuggestion (← getRef) source

end PrimeCert.Meta
