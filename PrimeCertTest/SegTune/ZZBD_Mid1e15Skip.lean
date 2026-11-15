/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole design halfway to the target

`ZZAH_OneGcd1024` at `10^15 + 1` with divisors to `3.17e7`: the settled shape, chunk 1024 and one
gcd, against `ZZBC_Mid1e15Route`.

This is the arm that said the advantage grows with depth rather than eroding, and the emitter's own
counts say why. Both things I expected happened: the skipped set grew about in proportion to the
divisors, and the certificate grew with it. What I had not expected is that the number of divisors
that actually strike grew far more slowly than the number of divisors, so the fraction the sweep
can skip rises with depth, and the marking saved outruns the certificate added by a wide margin.

The wide-band lemma figure is where to look: it is most of the difference between the two arms,
and it is the part the sweep replaces.

Written up here because goldbach generated it on a box that has since been terminated, from `ZZAH`
with only the start, the fuel and the sieve bound changed.

Pair with `ZZBC_Mid1e15Route`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZBD_Mid1e15Skip

run_sieve 31700000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3523 1000000000000001 4194304 10566666 8192 0 65536 31700000

end PrimeCert.SegTune.ZZBD_Mid1e15Skip
