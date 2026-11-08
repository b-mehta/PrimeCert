/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCertTest.PopProbe.Defs

/-! # The chunked count over a bitset of 1000000 bits

The pair with `PrimeCertTest/PopProbe/Size1e7.lean`, which is the same fold over ten times the
bitset. Each block of the fold shifts the whole bitset, so the two kernel totals say how the cost
moves with the bitset rather than with the number of blocks: ten times for one, a hundred for the
other.
-/

namespace PrimeCert.PopProbe.Size1e6

set_option maxRecDepth 4000000 in
run_pop_probe 1000000 1

end PrimeCert.PopProbe.Size1e6
