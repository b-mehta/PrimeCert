/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCertTest.PopProbe.Defs

/-! # The same window of 262144 bits counted 64 bits at a time

4096 chunks, each one shift of the whole window, one mask, one `popc64K` and one addition. The
other arm is `PrimeCertTest/PopProbe/ArmWindow.lean`.
-/

namespace PrimeCert.PopProbe.Chunks

set_option maxRecDepth 4000000 in
run_pop_probe 262144 1

end PrimeCert.PopProbe.Chunks
