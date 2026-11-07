/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.LeafProbe

/-! # The same walked leaves, from one sieve rather than one each

`W4797_1024.lean` sieves a fresh window for every leaf, which no run would do; this sieves the
whole span once and cuts the windows from it. The two emit identical statements, so the
difference between them is what per-leaf sieving costs, which is the part of a leaf's wall that
belongs to the probe rather than to the method.
-/

namespace PrimeCert.LeafEmit.Shared

set_option maxRecDepth 4000000 in
run_leaf_walk_shared 336000000 128 1024 4797

end PrimeCert.LeafEmit.Shared
