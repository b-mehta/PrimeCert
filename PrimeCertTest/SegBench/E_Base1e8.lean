/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # Segment benchmark: the target case

A window at `10^16 + 1` sieved by every prime up to `10^8`. Since `(10^8)^2 = 10^16`, this is the
base depth at which the survivors are prime rather than merely free of small factors.

This file builds the `10^8` sieve first, so it carries the whole `PrimeCertTest.SieveVerify1e8`
cost before the segment starts. It has never been run. Run it alone.

`len = 16384` gives 2035 chain links, under the 2605 that is known to be accepted; see the chain
depth table in `README.md`. Each batch is correspondingly large, and what that costs here has not
been measured.
-/

namespace PrimeCert.SegBench.E_Base1e8

run_sieve 100000000

run_segment 10000000000000001 1024 33333333 16384 100000000

end PrimeCert.SegBench.E_Base1e8
