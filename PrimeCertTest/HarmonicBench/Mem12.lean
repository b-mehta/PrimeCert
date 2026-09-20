/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.PrimeHarmonic
public meta import PrimeCert.SegmentedSieve

/-! # Twelve segments in one file, to see how a file's peak grows with what it holds

`Mem48` is the same thing with four times as many segments. If the peak is four times larger the
literals a file accumulates are what drives it, and cutting the range into more files would lower
the summed peak; if the peak barely moves, the count of files is the wrong thing to change.
-/

namespace PrimeCert.Mem12

set_option maxRecDepth 4000000 in
set_option Elab.async false in
run_harmonic_series 1000000001 1048576 100003 20 2048 1536 12 15

end PrimeCert.Mem12
