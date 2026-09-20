/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-! # The floor a bench process holds before it sums anything

Four lean processes on a runner hold about 4.8 GB between them before any segment is summed, and
staggering their starts cannot touch it. These files carry one import chain each and no
declarations, so the `floor` job's maximum resident figures say which import the floor is in. The
sieve session found their own floor was nearly all one correctness file, and cut 0.18 GB a process
by moving a single lemma out of a heavier import.
-/
