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
dead for the price of one run rather than a week of proofs.

**Priced 2026-11-12, and the kernel side is cheap: the cost has moved to the emitter.** Fresh
c7i.8xlarge, `run.sh 3`, load about 1, split by `run.sh`'s own rows. Sixty-four gcds cost
**1.88-1.90 s** of `addDecl` against `WA_Narrow`'s **66.1-66.8 s**, of which the batch lemmas this
would replace are **44.4-44.8 s**. Peak 0.96 GB against 1.72.

Against that, the window command takes **64.0-64.3 s** here against 72.3-73.1 for `WA_Narrow`, and
every batch and slice lemma row is zero, so that 64 s is this case building the two numbers and
nothing else. The next thing to measure is how that 64 s divides between `primorialOver`, which is
the same for every window of a run and so can be built once, and `sliceProduct`, which depends on
the window's survivors and cannot. Only the second is a per-window cost, and whether the direction
lives or dies turns on it.

**Split and measured, and the direction lives.** Same box and settings, three rounds: window
**37.3-38.4 s**, primorial **21.9-22.5 s**, slice products **2.01 s**, covering 97% of the 63.3-64.1
window command.

Read it carefully, because two of those three are not costs of the design. The primorial is the
same for every window of a run and is built once. The 37-38 s window build is an artefact of this
probe: it uses the plain `segLoopC` twin over every divisor in one go, where the banded route
`run_segment` now takes does the same job with the stripe twins in about 6 s (`WA_Narrow`: window
71.9-72.3 s against kernel 65.5-65.9).

**So the per-window cost the design would add is 2.01 s of slice products plus 1.85 s of kernel,
against the 65.5 s of kernel a window costs today.** That is the largest remaining idea by a wide
margin.

**But read what the gcd here actually says, because it is weaker than it looks.** `bits` is the
window sieved by *every* divisor at indices `1 … fuel`, and `bigP` is the product of the sieve
primes in `(32768, value fuel]`. Every prime in `bigP` has therefore already been swept out of
`bits`, so the gcd is 1 for a trivial reason and tells us nothing the sieve had not established
before the gcd was stated.

So the timings above price a `Nat.gcd` at these sizes, which is a real and reusable number, and
they are **not** evidence that a gcd can replace sieving work. A window sieved only by the small
primes still holds survivors divisible by the large ones — two factors above 32768 multiply to
something in range — so for a partially sieved window the gcd would simply not be 1.

What would have to be designed, and has not been, is a statement that is both cheap and
informative. One shape worth pricing: state the window literal, certify by one gcd a slice that
every position it keeps is prime, and justify every position it drops with a factor the emitter
supplies and the kernel checks. That is a different cost model from this probe's and nobody has
measured it. -/

namespace PrimeCert.SegTune.ZZQ_GcdPrice

run_sieve 10000000

run_segment_variant 75 100000000000001 4194304 333333 8192 10000000

end PrimeCert.SegTune.ZZQ_GcdPrice
