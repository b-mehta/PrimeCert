/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Does the sweep still get the window right off a shallower base?

`parts 49162`: the base built to `Wm1/128` instead of `Wm1/8`, sweeping from the eight-strike
band, with the emitter's self-check on and nothing else emitted.

This runs before the timing arm, not after it. The last knob I added to this sweep went out with
an argument for why it stayed sound and nothing checking it, and it was wrong — `wideHits` tested
only the two seeds, which is complete for the wide band and not a band lower. The argument here is
the same one that held: a base with more live bits than the finished window can only make a
divisor look like a striker, never the reverse. The counting agrees, `Wm1/128` giving the
identical strike set at `10^14` and `10^15`. Neither is the emitter rebuilding the window from the
marked subset and refusing to emit if it differs, which is what this does.

`pbase 2` turns the check on and the gcds off, and the low digits stop below the record
certificate, so the run is the marking pass, the sweep, the check and the route.

Timings here mean nothing: the check is a second full marking pass production never does.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBJ_ShallowBaseCheck

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 49162 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZBJ_ShallowBaseCheck
