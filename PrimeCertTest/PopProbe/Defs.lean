/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import PrimeCert.PrimeHarmonic

/-! # Two set-bit counts over one window, each in its own file

`popK n w` counts an `n`-bit window in one declaration, by masking stages widening to 32-bit
fields and a digit sum. The other way counts 64 bits at a time and sums the results, which is the
shape a `popc64K` consumer emits. `run_pop_probe bits arm` emits the equation for one arm over a
window built from a fixed generator, so the two arms see the same window and each gets its own
file and its own process.

Arm `0` is `popK`. Arm `1` is the fold over 64-bit chunks.
-/

namespace PrimeCert.PopProbe

open Lean Elab Command Meta

/-- The set bits of a 64-bit value, by masking stages and one multiplication reading the top
byte. -/
@[expose] public def popc64K (v : Nat) : Nat :=
  let a := v.sub ((v.shiftRight (nat_lit 1)).land (nat_lit 0x5555555555555555))
  let b := (a.land (nat_lit 0x3333333333333333)).add
    ((a.shiftRight (nat_lit 2)).land (nat_lit 0x3333333333333333))
  let c := (b.add (b.shiftRight (nat_lit 4))).land (nat_lit 0x0f0f0f0f0f0f0f0f)
  ((c.mul (nat_lit 0x0101010101010101)).shiftRight (nat_lit 56)).land (nat_lit 0xff)

/-- The set bits of `b` over `fuel` blocks of 64 positions from block `start`, one block at a
time. Each step shifts the whole of `b`, masks 64 bits off it, counts those and adds. -/
@[expose] public noncomputable def popcLoopK (b acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a ↦
    a.add
      (popc64K
        ((b.shiftRight ((start.add i).mul (nat_lit 64))).land
          (((nat_lit 1).shiftLeft (nat_lit 64)).sub (nat_lit 1))))

/-- Add `name : type := value` as a theorem, with no source statement to elaborate. -/
meta def addProbeThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- `b = true` as a proposition, for a `Bool`-valued `b`. -/
meta def mkBoolTrue (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- A window of `bits` bits from a fixed multiplicative generator, so every arm sees the same one,
together with the number of bits it sets. -/
meta def probeWindow (bits : Nat) : Nat × Nat := Id.run do
  let mut w := 0
  let mut x : Nat := 0x2545F4914F6CDD1D
  let mut ones := 0
  for i in [0:bits] do
    x := (x * 6364136223846793005 + 1442695040888963407) % (1 <<< 64)
    if (x >>> 33) % 2 == 1 then
      w := w ||| (1 <<< i)
      ones := ones + 1
  return (w, ones)

/-- Emit the equation for one arm over the window of `bits` bits. -/
meta def runPopProbe (bits arm : Nat) : MetaM Unit := do
  if bits % 64 != 0 then
    throwError "run_pop_probe: {bits} is not a multiple of 64"
  let (w, ones) := probeWindow bits
  let ns ← getCurrNamespace
  let lhs := if arm == 0
    then mkApp2 (mkConst ``popK) (mkRawNatLit bits) (mkRawNatLit w)
    else mkAppN (mkConst ``popcLoopK)
      #[mkRawNatLit w, mkRawNatLit 0, mkRawNatLit 0, mkRawNatLit (bits / 64)]
  let name := ns ++ Name.mkSimple (if arm == 0 then "countByWindow" else "countByChunks")
  addProbeThm name
    (mkBoolTrue (mkApp2 (mkConst ``Nat.beq) lhs (mkRawNatLit ones)))
    Lean.reflBoolTrue
  logInfo s!"run_pop_probe: {bits} bits, {ones} set, arm \
{if arm == 0 then "popK over the whole window" else s!"popc64K over {bits / 64} chunks"}"

/-- `run_pop_probe bits arm` emits one arm's equation (see `runPopProbe`). -/
elab "run_pop_probe" bStx:num aStx:num : command =>
  liftTermElabM <| runPopProbe bStx.getNat aStx.getNat

end PrimeCert.PopProbe
