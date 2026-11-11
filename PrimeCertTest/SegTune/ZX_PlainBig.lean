/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # A window on the plain path, where the bit test reads the whole base sieve

`run_segment_variant` states each batch against the batch's own slice, about a kilobyte, so the
order of the operands in `testBitK` does not show there: measured as a null on `WA_Narrow`, four
runs an arm. The plain `run_segment` states each batch against the whole base sieve instead, so at
a ten million base the tested operand is a few hundred kilobytes and is read once a divisor. That
is the regime where operand order was measured to matter a great deal elsewhere, 42 microseconds
against 0.6 for a megabyte `land`.

This case is deliberately small except in the one dimension under test: a quarter-width window and
a tenth of the divisors, with the full base sieve, so the question is asked cheaply.

Run it as a commit pair over `PrimeCert/Sieve.lean`, `82110f9` (bitset first) against `7ba4623`
(probe first). The two differ in that one line and nothing else. -/

namespace PrimeCert.SegTune.ZX_PlainBig

run_sieve 10000000

run_segment 100000000000001 1048576 100000 8192 10000000

end PrimeCert.SegTune.ZX_PlainBig
