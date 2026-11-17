/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve

/-! # The base sieve to `10^7`, as its own module

Nothing but the sieve, so that a case can import it rather than build it, as `Base1e17` does for
the `3.163 * 10^8` one. This is the smallest of the three points the import floor is read at.

Throwaway. -/

namespace PrimeCert.SegTune.Base1e7

run_sieve 10000000

end PrimeCert.SegTune.Base1e7
