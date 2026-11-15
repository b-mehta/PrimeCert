/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The certificate stated over records

`parts 20`, which is `parts 4` plus 16: the gcd equations alone, no marking route, no self-check,
the strike set swept from the wide band, and the certificate stated over **records** rather than
over the window's bits.

This is the question the two earlier certificate shapes failed to answer. Both walked the window
one bit at a time, about 8 million `testBitK` calls against a multi-megabit literal, and both were
killed past 40 GB with the kernel barely started — as a linear fold and as a balanced tree alike,
which is what showed the multiplication structure was never the cost. The route is affordable
because `stripeUpToK` walks the records it is given and never inspects the window. So does this:
each statement shifts a 256-record chunk, about 512 bytes, not a 512 KB window.

Counted beforehand, so the log can be checked rather than trusted: about 1527 statements on the
live side, the window's 390802 primes in chunks of 256.

**Timing only.** The skipped product is supplied as a literal rather than established from its own
records, so this measures whether the shape is affordable before the work of proving it goes in.
Every statement emitted is kernel-checked regardless.

Pair with `ZZV_WideSweepNoCheck`, one job, peak each. The number that decides this: the sweep saves
about 50 s of kernel, so the certificate has to cost less than that to be worth having at all.

Throwaway. -/

namespace PrimeCert.SegTune.ZZY_RecordCert

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 20 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZY_RecordCert
