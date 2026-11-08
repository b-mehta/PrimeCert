/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCertTest.PopProbe.Defs

/-! # The chunked count over a bitset of 10000000 bits

Ten times the bitset of `PrimeCertTest/PopProbe/Size1e6.lean` and ten times the blocks. Run both
on the same machine and read the `[Kernel]` line from each.
-/

namespace PrimeCert.PopProbe.Size1e7

set_option maxRecDepth 40000000 in
run_pop_probe 10000000 1

end PrimeCert.PopProbe.Size1e7
