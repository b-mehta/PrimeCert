/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.LeafProbe

/-! # The same 128 leaves, emitted and walked

`L4797_1024.lean` emits each leaf as a fold over every position of its prefix; this emits each as
a walk over the gaps between survivors, which is the statement the production path proves. As
source the walk lost to the fold on wall, but it carried far more text; emitted, both lose their
source and the kernel figures should decide instead.
-/

namespace PrimeCert.LeafEmit.Walk

set_option maxRecDepth 4000000 in
run_leaf_walk 336000000 128 1024 4797

end PrimeCert.LeafEmit.Walk
