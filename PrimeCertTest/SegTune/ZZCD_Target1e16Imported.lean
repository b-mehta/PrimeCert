/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCertTest.SegTune.S8_Sieve1e8

/-! # The settled window at `10^16`, over a base that was imported rather than built

`ZZBB_Target1e16Skip` with one change: the `10^8` base comes from `S8_Sieve1e8`'s olean instead of
being built in the file. Run beside `ZZBB` in one job, the pair says what reading an imported base
costs against reading one the same file just built, at a depth that fits on a free runner.

Worth asking because importing turned out to be free until something reads it: a case that imports
this base and runs nothing peaks 1020 MiB, the same as one importing no sieve at all. Whatever the
base costs is charged at the read, and `runSegmentSkip` now prints the two lines around it.

The same question at `3.163 * 10^8` can no longer be asked here, since writing that base to an
olean peaks 14103956 KiB on its own and the dependency watchdog stops it.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCD_Target1e16Imported

set_option maxRecDepth 1000000 in
run_segment_skip_part 3198403 10000000000000001 4194304 33333333 65536 0 65536 100000000

end PrimeCert.SegTune.ZZCD_Target1e16Imported
