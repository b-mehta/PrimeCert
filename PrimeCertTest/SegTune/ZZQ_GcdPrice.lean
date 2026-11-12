/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public meta import PrimeCert.Meta.Sieve
public meta import PrimeCert.SegmentedSieve

/-! # What a gcd certificate would cost, before anyone designs one

The largest idea anyone has put forward for the forty seconds of marking is to stop building a
mask for every divisor: sieve by the small ones only, then let one `Nat.gcd` per slice certify
that nothing left in that slice has a factor in the rest of the range. Its projection is the
kernel from 66 seconds to about 23, and its proof obligations are the heaviest of anything
proposed, so the design should not be written until the one unknown is priced.

That unknown is what a `Nat.gcd` costs at these sizes. `Nat.gcd` is already on the kernel's fast
path, so this needs no new definitions: mode 75 builds the two numbers the real design would use,
the product of a slice's survivors against the product of the base primes above 32768, and states
`Nat.gcd a b = 1` once per slice. It logs both sizes.

**This proves nothing about the sieve.** It is a stopwatch. Read the kernel seconds against
`WA_Narrow`'s 40 seconds of batch lemmas: if sixty-four gcds cost more than that, the direction is
dead for the price of one run rather than a week of proofs. -/

namespace PrimeCert.SegTune.ZZQ_GcdPrice

run_sieve 10000000

run_segment_variant 75 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZZQ_GcdPrice
