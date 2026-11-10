/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The same window on the wheel of thirty

The other arm of the pair described in `Z6_Wheel6`: the same width and the same divisors, with a
bit standing for one of the eight residues coprime to 30 rather than one of the two coprime to 6.
The window therefore covers 15728640 integers against 12582912, a quarter further, while a
divisor's mask now starts from eight seeds instead of two and needs two fewer doubling rounds. -/

namespace PrimeCert.SegTune.Z7_Wheel30

run_wheel 30 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.Z7_Wheel30
