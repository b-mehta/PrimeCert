/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.LeafProbe

/-! # The same 128 leaves, emitted rather than parsed

`PrimeCertTest/LeafNarrow/L4797_1024.lean` states these leaves as source theorems closed by
`quickRfl`; `PrimeCertTest/LeafRaw/L4797_1024.lean` does the same with raw numerals and the
linters off. This emits them, so the elaborator parses no statement, builds no `OfNat` numeral
and keeps no info tree for them. The kernel checks the same thing in all three.
-/

namespace PrimeCert.LeafEmit

set_option maxRecDepth 4000000 in
run_leaf_probe 336000000 128 1024 4797

end PrimeCert.LeafEmit
