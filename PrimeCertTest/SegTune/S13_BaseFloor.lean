/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCertTest.SegTune.Base1e17

/-! # What an imported base costs before anything uses it

Imports the `3.163 * 10^8` sieve and runs nothing. The segment command is imported so that the
file is the same shape as a case, and `run_segment_skip_part` is absent so that nothing reads the
base.

The question is a number nobody has. Building that base in a case puts 6400 MiB resident at
entry; importing it instead puts 5508 MiB, so 892 MiB is the elaboration and the other 5.5 GiB
survives the import. The literal itself is about 13 MB. Something holds thousands of times that,
and whatever it is also decides whether a bigger base can ever be afforded: at `10^9` the base
takes the runner down rather than merely crossing `run.sh`'s limit.

This case reports the floor alone, with no window, no sweep and no certificate on top of it.

Throwaway. -/

namespace PrimeCert.SegTune.S13_BaseFloor

end PrimeCert.SegTune.S13_BaseFloor
