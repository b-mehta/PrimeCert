/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve
public meta import PrimeCertTest.SegTune.S8_Sieve1e8

/-! # What an imported `10^8` base costs before anything uses it

The companion to `S13_BaseFloor`, which does the same for the `3.163 * 10^8` base. Both import a
sieve and run nothing: no window, no sweep, no certificate.

Two floors read in one job answer a question one cannot. If the floor is close to proportional to
the literal, the cost is the literal and a bigger base is priced by its size; if the two floors are
close to each other, most of it is a fixed charge for having a sieve imported at all, and the base
is not what a higher `N` has to pay for.

Throwaway. -/

namespace PrimeCert.SegTune.S14_BaseFloor1e8

end PrimeCert.SegTune.S14_BaseFloor1e8
