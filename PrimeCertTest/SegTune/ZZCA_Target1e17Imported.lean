/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCert.SkipSound
public meta import PrimeCertTest.SegTune.Base1e17

/-! # A window at `10^17` with the base imported rather than built here

`ZZBP_Target1e17Skip` with its `run_sieve` line removed and the same sieve imported from
`Base1e17` instead. Everything else is identical, `parts 3329987`.

The phase log of the killed `ZZBP` put 6522 MiB resident at entry, before the sweep, the window or
the certificate, and the base's literal is about 13 MB. So either the sieve's own elaboration is
holding that memory, in which case importing it drops the figure and the window may fit, or it is
not, in which case this case dies at the same place and the 6.5 GiB is something else.

Pair with `ZZBP_Target1e17Skip`, one job, so both figures are from one machine. Read the entry
line of the phase log first; the peak only matters if the entry moves.

Throwaway. -/

namespace PrimeCert.SegTune.ZZCA_Target1e17Imported

set_option maxRecDepth 1000000 in
run_segment_skip_part 3329987 100000000000000001 4194304 105433333 65536 0 65536 316300000

end PrimeCert.SegTune.ZZCA_Target1e17Imported
