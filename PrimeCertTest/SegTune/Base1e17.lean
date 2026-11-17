/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve

/-! # The base sieve to `3.163 * 10^8`, as its own module

Nothing but the sieve, so that a case can import it rather than build it. `run_sieve` registers
the cache in `sieveCacheExt` and marks the literal `forceExpose`, which its own comment says is
there so a module consumer can read it, so the arrangement is the one the command was built for.

The question it exists to answer: at `10^17` a case that builds this in the same file is at
6522 MiB resident before the window is touched, while the literal itself is about 13 MB. Imported,
it arrives in an olean instead of being elaborated in place. Whether that is where the 6.5 GiB
goes is what `ZZCA_Target1e17Imported` against `ZZBP_Target1e17Skip` says.

Throwaway. -/

namespace PrimeCert.SegTune.Base1e17

run_sieve 316300000

end PrimeCert.SegTune.Base1e17
