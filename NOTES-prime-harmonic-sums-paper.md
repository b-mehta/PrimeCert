# Bach, Klyve and Sorenson, "Computing prime harmonic sums"

Mathematics of Computation 78 (2009), pages 2283 to 2305. Parked for now; this note records what the
paper does in case the sum of 1/p work returns to it.

## What it computes

The sum of 1/p over primes p up to x, in time about x^(2/3) and space about x^(1/3), by adapting the
Meissel-Lehmer / Lagarias-Miller-Odlyzko prime-counting method to weights 1/p. The headline result is
the first crossing of 4: the sum up to 1801241230056600467 is below 4 and the sum up to
1801241230056600523 is above it (p. 2284 and section 8).

## The identity

Let a = π(x^(1/3)), so p_a is the largest prime up to x^(1/3). Let φ(x, a) be the sum of 1/n over
n ≤ x with no prime factor up to p_a, including n = 1. Let S₂ be the sum of 1/(pq) over primes
p_a < p ≤ q with pq ≤ x. Then (equation 2.7, p. 2285)

    ∑_{p ≤ x} 1/p = ∑_{p ≤ p_a} 1/p − S₂ + φ(x, a) − 1.

φ(x, a) is expanded by φ(x, a) = φ(x, a−1) − (1/p_a) φ(x/p_a, a−1) (2.2) and split into
"ordinary" terms (3.3), about (4/π²) x^(1/3) of them, each needing log y and Euler's constant, and
"special" terms, about π(x^(1/3))²/2 of them, each a partial-sieve value (section 3.6).

## What each piece needs

| piece | work |
|---|---|
| ∑_{p ≤ p_a} 1/p | primes up to x^(1/3) |
| S₂ | primes up to x^(2/3), running totals of 1/q at x/p and at p for each prime p in (p_a, √x] |
| special terms | a segmented sieve over [0, x^(2/3)) in blocks of x^(1/3), with prefix sums |
| ordinary terms | rational bounds on log y for each term and on γ + log 2 |

At x = 10^12 that is a sieve to 10^8, 77269 S₂ checkpoints, about 7.6 × 10^5 special terms and
about 4053 ordinary terms (the paper's formulas; counts computed by a subagent).

## Arithmetic

Double-double floating point (about 30 digits), with an error analysis the authors describe as "just
short of rigorous proof" (section 9). The ordinary terms need analysis beyond rational arithmetic.

## Separately usable

Equation (8.2): over a window starting at o, with c primes and s the sum of their offsets from o,
∑ 1/p ≈ c/o − s/o², with the error bounded rigorously by the next term of an alternating series.

**Built and measured on 2026-09-18.** No alternating-series machinery is needed: `0 ≤ (o − p)²`
gives the lower bound and `0 ≤ (p − o)³` the upper, so with C the count, V = ∑p and Q = ∑p²,

    (2oC − V)/o² ≤ ∑ 1/p ≤ (3o²C − 3oV + Q)/o³.

Folding the offsets d = p − o instead gives (Co − D)/o² and (Co² − oD + E)/o³ with D = ∑d,
E = ∑d²; the two are the same enclosure. `PrimeHarmonic.lean` has both, plus a two-fold version
bounding Q by top·V and a version using the count alone, as emitter forms 8 to 11.

Result: at a window starting at 1e12 it is 6% slower than dividing 10²⁰ by each prime and gives an
interval 2.2 million times narrower (10⁻²⁰ against 2.85e-16). Below about 1e10 it is both slower
and wider. It is not a speed lever, because crossing off composites is 83% of a window's kernel
time and all the summing is 17%. Numbers in the project memory.

## Why it is parked

The ordinary terms need proved bounds on logarithms and Euler's constant, which is a separate proof
project. The current approach sums every prime directly.
