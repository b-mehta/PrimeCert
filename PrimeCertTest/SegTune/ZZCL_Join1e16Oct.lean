/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound

/-! # The proved window at `10^16`, the skipped side eight records a leaf

`ZZBY_Join1e16Quad` with `(parts / 16777216) % 2` set, which states the skipped chunks' products
and assemblies over 128-bit words of eight records instead of 64-bit words of four. Everything
else is the same, the live side included.

Asked because that is the change that has paid twice. Going from one record a leaf to four took
the assembly down 58%, and at `10^16` the skipped side is where the certificate's time is: of
`ZZBY`'s kernel, the records are 31 to 41 s and the assembly 27 to 39 s, depending on the runner,
out of about 195 to 270.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCL_Join1e16Oct

run_sieve 100000000

set_option maxRecDepth 1000000 in
run_segment_skip_part 20106691 10000000000000001 4194304 33333333 65536 0 65536 100000000

#print axioms segEqAll_10000000000000001_4194304_33333333

end PrimeCert.SegTune.ZZCL_Join1e16Oct
