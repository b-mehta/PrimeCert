/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^16`, the skipped side sixteen records a leaf

`ZZCL_Join1e16Oct` with `(parts / 33554432) % 2` set as well, which states the skipped chunks'
products and assemblies over 256-bit words of sixteen records instead of 128-bit words of eight.

One step further along the line that has paid twice: one record a leaf to four took the assembly
down 58%, four to eight took the records 10.1% and the assembly 9.3%, and the whole kernel 2.6%.

Settled: four rounds a side in one job, every round separating, put this 6.3 to 8.2% below the
four-a-leaf window on kernel, 18% on the skipped records, 21% on the assembly and 0.87% on peak.
So `parts 53661123` is what a joined run at `10^16` asks for, and `ZZBY_Join1e16Quad` is kept as
the four-a-leaf arm it was measured against rather than as anything to run.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCN_Join1e16Hex

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 53661123 10000000000000001 4194304 33333333 65536 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZCN_Join1e16Hex
