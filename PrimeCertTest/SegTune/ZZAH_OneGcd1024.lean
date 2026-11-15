/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Both winners at once

`parts 3523`: a chunk of 1024 records and one gcd for the window.

The two were measured apart and each won on kernel and processor together, 1024 over 512 by about
3.5 s and the single gcd over one a chunk by about 11 s. They are independent knobs, so this is
the arm that says whether they add.

There is a reason they might not. The single gcd removes the per-chunk gcds, which is where the
chunk size did most of its work, so the saving from doubling the chunk may be smaller once the
gcds are gone. Equally the chunk statements that remain are products and assemblies, and those
still halve.

Written up here because goldbach generated the same arm on the box; this is it in the repository
so it is not lost with the box.

Pair with `ZZAG_OneGcd` and `ZZH_FullWindow28`, one job, alternating, peak each.

Throwaway. -/

namespace PrimeCert.SegTune.ZZAH_OneGcd1024

run_sieve 10000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 3523 100000000000001 4194304 3333333 8192 0 65536 10000000

end PrimeCert.SegTune.ZZAH_OneGcd1024
