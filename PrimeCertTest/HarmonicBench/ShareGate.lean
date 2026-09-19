/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.QuickRfl

/-! # Does a value passed to a helper and used twice inside it reduce once or twice?

Three statements the kernel settles, over the same expensive fold `foldK 200000`. `both` writes
the fold twice, `helper` writes it once and passes it to a function whose body uses its argument
twice, `once` writes it once. Comparing the three separates a term the kernel evaluates twice
from one it evaluates once, which decides how the sieving definitions should thread the values
they use more than once.
-/

namespace PrimeCert.ShareGate

/-- An expensive fold: `3 ^ n` modulo `1000000007`, by `n` multiplications. -/
@[expose] public noncomputable def foldK (n : Nat) : Nat :=
  n.rec (nat_lit 1) fun _ a ↦ (a.mul (nat_lit 3)).mod (nat_lit 1000000007)

/-- A helper using its argument twice. -/
@[expose] public def twiceK (x : Nat) : Nat := Nat.add x x

set_option maxRecDepth 4000000 in
theorem once : Nat.beq (foldK (nat_lit 200000)) (nat_lit 646068149) = true := by quickRfl

set_option maxRecDepth 4000000 in
theorem helper :
    Nat.beq (twiceK (foldK (nat_lit 200000))) (nat_lit 1292136298) = true := by quickRfl

set_option maxRecDepth 4000000 in
theorem both :
    Nat.beq (Nat.add (foldK (nat_lit 200000)) (foldK (nat_lit 200000)))
      (nat_lit 1292136298) = true := by quickRfl

/-- Whether `Nat.log2` reduces on a literal in a kernel-checked position. -/
theorem logTwo : Nat.beq (Nat.log2 (nat_lit 262143)) (nat_lit 17) = true := by quickRfl

end PrimeCert.ShareGate
