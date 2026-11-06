/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCertTest.Carry4.Part0
public import PrimeCertTest.Carry4.Part1
public import PrimeCertTest.Carry4.Part2
public import PrimeCertTest.Carry4.Part3
public meta import PrimeCert.Meta.QuickRfl

/-! # Four ranges proved in four jobs, joined in a fifth

Each `Part` file proves one range and is compiled by its own job in the `carry4` workflow; this
file imports their compiled output and adds them, so the only work here is the kernel checking six
additions of literals. Nothing is resieved and nothing is resummed, which is what the record run
needs if its four pieces are ever to meet in one theorem rather than in a script.
-/

namespace PrimeCert.Carry4

/-- The four ranges, added. -/
public theorem joined :
    PrimeRecipRange 1000000001 1012582913 60330256703098169 4194304 100000000000000000000 := by
  have k₁ : PrimeRecipRange 1000000001 1006291457 30262244268358938 2097152
      100000000000000000000 :=
    primeRecipRange_add (by quickRfl) (by quickRfl)
      primeRecipRange_1000000001_1003145729_20 primeRecipRange_1003145729_1006291457_20
      (by quickRfl) (by quickRfl)
  have k₂ : PrimeRecipRange 1000000001 1009437185 45303975089828186 3145728
      100000000000000000000 :=
    primeRecipRange_add (by quickRfl) (by quickRfl) k₁
      primeRecipRange_1006291457_1009437185_20 (by quickRfl) (by quickRfl)
  exact primeRecipRange_add (by quickRfl) (by quickRfl) k₂
    primeRecipRange_1009437185_1012582913_20 (by quickRfl) (by quickRfl)

end PrimeCert.Carry4
