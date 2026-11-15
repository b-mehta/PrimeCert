/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The sweep taken down one band

`parts 11715`: `ZZAH_OneGcd1024` with the sweep starting at the four-strike band rather than at
the wide band.

Counting says the band is worth asking about. `scripts/band_skippable.py` tests every band against
the same base the sweep uses and finds the four-strike band 60.2% skippable at `10^14` and 64.2%
at `10^15` — 44281 and 47238 divisors that strike nothing live and are marked anyway. The wide
band is 85.5% and 93.7%, so this band is less rewarding, but it is not the barren one the earlier
base-depth count might suggest. Those were different questions: that one asked whether marking
these bands changes what the wide band can skip, and the answer was no.

What it trades: the marking loses those divisors' strike records, and the certificate gains them,
since every skipped divisor has to be carried in the skipped product and its records. The skip
side grows by about a tenth. Which way that comes out is why this is an arm and not a patch.

Pair with `ZZAH_OneGcd1024`, one job, alternating, peak each. The lines to read are the swept-band
line, `marked … skipped … of …`, and the wide-band lemma figure.

If it wins, `parts 19907` is the same thing taken down one band further, to where only the masked
small band is marked plainly.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBE_SweepFour

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 11715 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZBE_SweepFour
