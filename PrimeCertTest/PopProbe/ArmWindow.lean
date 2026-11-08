/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCertTest.PopProbe.Defs

/-! # One window of 262144 bits counted by `popK`

The other arm is `PrimeCertTest/PopProbe/ArmChunks.lean`, which counts the same window 64 bits at
a time. Each arm has its own file and its own process, so the two kernel totals are comparable.
-/

namespace PrimeCert.PopProbe.Window

set_option maxRecDepth 4000000 in
run_pop_probe 262144 0

end PrimeCert.PopProbe.Window
