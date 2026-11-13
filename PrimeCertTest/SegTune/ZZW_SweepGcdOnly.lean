/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # What the certificate costs on its own, over the swept skip set

`parts 12`: the 64 gcd equations and no marking route, with the strike set swept from the wide band
and no self-check.

This is the last unmeasured piece. The sweep saves kernel by not marking 435226 divisors, and
something still has to establish that those divisors strike nothing, or the sieve proves less than
it did. Two shapes were considered and only one survives on paper:

* **Enumerating** — build the skipped divisors' strike positions and show the window is empty at
  each. The wide band's own marking is 16.0 s for the 73742 strikers against 66.4-67.1 s for all
  508968, so building the positions of the 435226 skipped ones costs about what the sweep saved.
  Self-defeating by construction, whatever it measures.
* **Aggregating** — one `Nat.gcd` a slice against the product of the skipped divisors. Nothing is
  built per divisor. This is that shape, and its cost has never been measured on its own: `ZZI`
  bundled it with the route and `ZZQ_SkipGcdOnly` never ran.

So the figure to read is the `skip gcds` column, which `run.sh` now reports apart from the batch
lemmas. Against the 50 s of kernel the sweep saves, that column says whether the design can be
made sound at a price worth paying, or whether the saving exists only while nothing is proved.

Note this arm does build the finished window, since the gcds are stated over it, so its processor
figure is not comparable with `ZZV_WideSweepNoCheck`'s.

Throwaway. -/

namespace PrimeCert.SegTune.ZZW_SweepGcdOnly

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 12 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZW_SweepGcdOnly
