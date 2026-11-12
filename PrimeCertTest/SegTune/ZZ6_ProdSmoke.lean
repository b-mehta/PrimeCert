/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does `run_segment` still emit what it always emitted

A small plain `run_segment` after it was moved onto the clamped marking. The batch lemmas are now
about `segLoopCK` and the chain is closed through `segEq_of_clamped`, but the two theorems the
command ends at, `segEq_…` on `segLoopK` and `segEqI_…` on `segRun`, are the ones it has always
emitted, so a consumer of the sieve sees no change. Elaborating this says the clamped chain really
does close them. Throwaway. -/

namespace PrimeCert.SegTune.ZZ6_ProdSmoke

run_segment 100000000000001 262144 20000 2048 1000000

-- The names, spelled out. A route change that renamed what the command emits would break every
-- consumer silently, so this fails the build rather than leaving it to be noticed later.
#check (segEq_100000000000001_262144_20000_2048)
#check (segEqI_100000000000001_262144_20000_2048)

end PrimeCert.SegTune.ZZ6_ProdSmoke
