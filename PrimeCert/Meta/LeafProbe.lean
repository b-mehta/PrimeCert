/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.Meta.PrimeHarmonic

/-!
# Leaves emitted rather than parsed

`PrimeCertTest/LeafProbe` states each leaf as a source theorem closed by `quickRfl`, so the
elaborator parses it, builds its numerals through `OfNat`, lints it and keeps an info tree for it.
A run emits its statements instead, and never pays any of that. `run_leaf_probe` emits the same
leaves the generated files hold, so the two can be timed against each other and the difference is
what stating a leaf in source costs.

`run_leaf_probe start count length b` emits `count` leaves of `length` wheel positions each,
beginning at position `start`, over an interval sieved by the first `b` primes.
-/

namespace PrimeCert

open Lean Elab Command Meta

/-- The `k`-th integer coprime to 6, as the emitter computes it. -/
meta def leafValue (k : Nat) : Nat := (k * 3 + 1) + k % 2

/-- Add `name : type := value` as a theorem, without a source statement to elaborate. -/
meta def addLeafThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- `b = true` as a proposition, for a `Bool`-valued `b`. -/
meta def mkBoolTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- The first `n` primes, by sieving an interval wide enough to hold them. -/
meta def firstPrimes (n : Nat) : Array Nat := Id.run do
  let mut limit := 256
  repeat
    let mut flags := Array.replicate (limit + 1) true
    flags := flags.set! 0 false
    flags := flags.set! 1 false
    for p in [2:limit + 1] do
      if flags[p]! then
        let mut m := p * p
        while m ≤ limit do
          flags := flags.set! m false
          m := m + p
    let mut out : Array Nat := #[]
    for i in [0:limit + 1] do
      if flags[i]! then out := out.push i
    if out.size ≥ n then return out.extract 0 n
    limit := limit * 2
  return #[]

/-- The window of positions `lo … lo + len - 1` whose numbers have no factor among `primes`,
and the scaled total over them. -/
meta def leafWindow (primes : Array Nat) (lo len S : Nat) : Nat × Nat := Id.run do
  let first := leafValue lo
  let last := leafValue (lo + len - 1)
  let mut live := Array.replicate len true
  for p in primes do
    if p > 3 then
      let mut m := ((first + p - 1) / p) * p
      while m ≤ last do
        let r := m % 6
        if r == 1 || r == 5 then
          let k := if r == 1 then 2 * ((m - 1) / 6) else 2 * ((m - 5) / 6) + 1
          live := live.set! (k - lo) false
        m := m + p
  let mut w := 0
  let mut tot := 0
  for i in [0:len] do
    if live[i]! then
      w := w ||| (1 <<< i)
      tot := tot + S / leafValue (lo + i)
  return (w, tot)

/-- Emit `count` leaves directly, with no source statement for the elaborator to parse. -/
meta def runLeafProbe (start count len b : Nat) : MetaM Unit := do
  let S := 10 ^ 20
  let primes := firstPrimes b
  let ns ← getCurrNamespace
  let mut lo := start
  for k in [0:count] do
    let (w, tot) := leafWindow primes lo len S
    let name := ns ++ Name.mkSimple s!"leaf_{k}"
    addLeafThm name
      (mkBoolTrue (mkApp2 (mkConst ``Nat.beq)
        (mkAppN (mkConst ``sumB)
          #[mkApp3 (mkConst ``recipAtW) (mkRawNatLit w) (mkRawNatLit lo) (mkRawNatLit S),
            mkRawNatLit 0, mkRawNatLit len, mkRawNatLit 1])
        (mkRawNatLit tot)))
      Lean.reflBoolTrue
    lo := lo + len
  logInfo s!"run_leaf_probe: {count} leaves of {len} positions from {start}, \
first {b} primes removed"

/-- The same leaves, each answered by walking the gaps between survivors rather than folding over
every position. The statement is the one `gapFoldK` proves, as the production path emits it. -/
meta def runLeafWalk (start count len b : Nat) : MetaM Unit := do
  let S := 10 ^ 20
  let primes := firstPrimes b
  let ns ← getCurrNamespace
  let P := 1 <<< (len + 1)
  let Q := 1 <<< 32
  let mut lo := start
  for k in [0:count] do
    let (w, _) := leafWindow primes lo len S
    -- the walk counts positions from one, so it reads the window against `lo - 1`
    let mut G := 0
    let mut c := 0
    let mut prev := 0
    for j in [0:len] do
      if (w >>> j) % 2 == 1 then
        G := G ||| ((j + 1 - prev) <<< (8 * c))
        prev := j + 1
        c := c + 1
    let mut pos := 0
    let mut bits := 0
    let mut acc := 0
    for i in [0:c] do
      pos := pos + ((G >>> (8 * i)) &&& 255)
      bits := bits ||| (1 <<< pos)
      acc := acc + S / leafValue (lo - 1 + pos)
    let R := bits + P * (pos + Q * acc)
    let name := ns ++ Name.mkSimple s!"leaf_{k}"
    addLeafThm name
      (mkBoolTrue (mkApp2 (mkConst ``Nat.beq)
        (mkAppN (mkConst ``gapFoldK)
          #[mkRawNatLit P, mkRawNatLit Q, mkRawNatLit (P * Q), mkRawNatLit 8, mkRawNatLit 255,
            mkRawNatLit G, mkRawNatLit (lo - 1), mkRawNatLit S, mkRawNatLit c])
        (mkRawNatLit R)))
      Lean.reflBoolTrue
    lo := lo + len
  logInfo s!"run_leaf_walk: {count} leaves of {len} positions from {start}, \
first {b} primes removed"

/-- The walked leaves again, with the whole span sieved once and the windows cut from it, which
is what a run does. Against `runLeafWalk`, which sieves a fresh window for each leaf, the
difference is what per-leaf sieving costs. -/
meta def runLeafWalkShared (start count len b : Nat) : MetaM Unit := do
  let S := 10 ^ 20
  let primes := firstPrimes b
  let ns ← getCurrNamespace
  let P := 1 <<< (len + 1)
  let Q := 1 <<< 32
  let span := count * len
  -- one sieve over the whole span
  let first := leafValue start
  let last := leafValue (start + span - 1)
  let mut live := Array.replicate span true
  for p in primes do
    if p > 3 then
      let mut m := ((first + p - 1) / p) * p
      while m ≤ last do
        let r := m % 6
        if r == 1 || r == 5 then
          let k := if r == 1 then 2 * ((m - 1) / 6) else 2 * ((m - 5) / 6) + 1
          live := live.set! (k - start) false
        m := m + p
  for k in [0:count] do
    let lo := start + k * len
    let mut G := 0
    let mut c := 0
    let mut prev := 0
    for j in [0:len] do
      if live[k * len + j]! then
        G := G ||| ((j + 1 - prev) <<< (8 * c))
        prev := j + 1
        c := c + 1
    let mut pos := 0
    let mut bits := 0
    let mut acc := 0
    for i in [0:c] do
      pos := pos + ((G >>> (8 * i)) &&& 255)
      bits := bits ||| (1 <<< pos)
      acc := acc + S / leafValue (lo - 1 + pos)
    let R := bits + P * (pos + Q * acc)
    let name := ns ++ Name.mkSimple s!"leaf_{k}"
    addLeafThm name
      (mkBoolTrue (mkApp2 (mkConst ``Nat.beq)
        (mkAppN (mkConst ``gapFoldK)
          #[mkRawNatLit P, mkRawNatLit Q, mkRawNatLit (P * Q), mkRawNatLit 8, mkRawNatLit 255,
            mkRawNatLit G, mkRawNatLit (lo - 1), mkRawNatLit S, mkRawNatLit c])
        (mkRawNatLit R)))
      Lean.reflBoolTrue
  logInfo s!"run_leaf_walk_shared: {count} leaves of {len} positions from {start}, \
one sieve over {span} positions, first {b} primes removed"

/-- `run_leaf_walk_shared start count length b`; see `runLeafWalkShared`. -/
elab "run_leaf_walk_shared" sStx:num cStx:num lStx:num bStx:num : command =>
  liftTermElabM <|
    runLeafWalkShared sStx.getNat cStx.getNat lStx.getNat bStx.getNat

/-- `run_leaf_probe start count length b`; see `runLeafProbe`. -/
elab "run_leaf_probe" sStx:num cStx:num lStx:num bStx:num : command =>
  liftTermElabM <|
    runLeafProbe sStx.getNat cStx.getNat lStx.getNat bStx.getNat

/-- `run_leaf_walk start count length b`; see `runLeafWalk`. -/
elab "run_leaf_walk" sStx:num cStx:num lStx:num bStx:num : command =>
  liftTermElabM <|
    runLeafWalk sStx.getNat cStx.getNat lStx.getNat bStx.getNat

end PrimeCert
