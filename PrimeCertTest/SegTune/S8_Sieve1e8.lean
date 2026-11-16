/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The base sieve to `10^8`, alone

The baseline arm for `S9_Sieve1e17Base`. `10^8` is the bound every `10^16` case uses, so this is
the base cost the design is known to carry, with no window work beside it.

Pair with `S9_Sieve1e17Base`, one job, so the two bases share a runner.

Throwaway. -/

namespace PrimeCert.SegTune.S8_Sieve1e8

run_sieve 100000000

end PrimeCert.SegTune.S8_Sieve1e8
