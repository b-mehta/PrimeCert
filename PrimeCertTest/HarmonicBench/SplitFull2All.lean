/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCertTest.HarmonicBench.Split8_Full
public import PrimeCertTest.HarmonicBench.Split8_Full1

/-! # Two of the four files of `Split8_Full`, for the file-count sweep

The sieve session's throughput saturates at two files: one, two, three and four give speedups of
1.00, 1.30, 1.30 and 1.29, so their third and fourth spend up to twice the memory for nothing.
Mine reaches 2.3 at four files but I have only ever compared one against four, so this file and
`SplitFull3All` fill in the middle and say where mine saturates. Where it does decides the file
count, which decides the per-file size, which is what sets the peak.
-/
