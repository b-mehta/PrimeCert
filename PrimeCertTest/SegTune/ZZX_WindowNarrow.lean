/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # The window at the width the sieve runs today

A plain `run_segment` at 4194304 bits, which covers 12582912 integers. Pair with
`ZZY_WindowWide`, the same run at twice the width.

Everything about a run is fixed by the height except the width of its window, and the width has
never been measured: it was chosen and the loop was tuned around it. The divisors are the same
either way, since they are the ones below the square root of the height, so a wider window does not
add work per divisor in the bands where a divisor strikes only once or twice; it halves the number
of windows those bands are paid for. Against that, a divisor whose mask is built to the window's
width pays twice as much per window, and a wider window moves more divisors into that band.

Compare kernel seconds divided by the integers covered, 3 times the window's width in bits, not
kernel seconds as reported. Report both arms' peak resident memory too: the wide arm holds a window
twice the size, and the width that wins on processor seconds is no use if it costs a run the
packing that the asynchronous-check measurement bought. -/

namespace PrimeCert.SegTune.ZZX_WindowNarrow

run_sieve 10000000

run_segment 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZZX_WindowNarrow
