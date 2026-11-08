/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Phi

/-! # A run at one bound carried on to the next

The sieved leaves of an expansion each want their own bound, and the bounds are every prime below
the cut. Sieving separately for each costs 42 times a single sweep at `x = 1e12`, so the sweep has
to be shared. `segRun_continue` is what shares it: the run at 103 is the run at 101 carried on for
the difference of the two bound indices, which is one step here since 101 and 103 are adjacent
wheel values.
-/

namespace PrimeCert.SegContinue

/-- The window of 1024 positions from 100001, sieved to 103, continuing the run sieved to 101. -/
example (s : ℕ) :
    Sieve.segRun s 100001 1024 103
      = Sieve.segLoopK s (Sieve.index 100001) 1023 (Sieve.segRun s 100001 1024 101)
          (1 + Sieve.index 101) 1 :=
  segRun_continue (by rfl)

end PrimeCert.SegContinue
