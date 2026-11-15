/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The whole design in one arm, certificate included

`parts 19`, which is `parts 3` plus 16: the marking route over the marked subset **and** the
record-stated certificate over the skipped set, swept strike set, no self-check. This is the shape
production would take, short of establishing the skipped product from its own records.

Why this rather than adding the two arms up: they share the marking pass and the window build, so
a sum counts those twice. `ZZY_RecordCert`'s 186 s of processor includes 102.8 s of marking that
`ZZV_WideSweepNoCheck`'s 141 s also includes.

What is known going in, same box, alternating:

* the sweep alone beats the production route by about 50 s of kernel;
* the certificate alone costs 25.2 s of kernel, peak 1.01 GB, no blowup — so **on kernel the
  design is ahead**, which neither earlier certificate shape ever got close to;
* processor is the open question, and the emitter is most of it: 102.8 s marking and, before this
  commit, 57.2 s building the skipped product sequentially. That product is now built pairwise.

Pair with `ZZH_FullWindow28`, one job, peak each. That is the comparison that says whether the
whole design, sound apart from the one asserted literal, beats what is in production today.

Throwaway. -/

namespace PrimeCert.SegTune.ZZZ_RecordFull

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 19 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZZ_RecordFull
