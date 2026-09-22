/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCertTest.HarmonicBench.Split8_Full

/-! # Whether one job can use a range theorem another job proved

`Split8_Full` sums eight segments and ends with a theorem covering `1000000001` to `1025165824`.
The `carry` workflow builds that file in one job, hands its compiled output to a second job as an
artifact, and compiles this file there. If this file elaborates, a later job can join pieces
proved by earlier ones, which is what a single Lean theorem for the whole sum needs.
-/

example := PrimeCert.primeRecipRange_1000000001_1025165825_20
