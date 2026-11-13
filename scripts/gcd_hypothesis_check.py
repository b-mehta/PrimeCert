"""Does the gcd certificate's hypothesis actually hold on a real window?

`segLoopK_eq_self_of_range` concludes that a range of divisors leaves the window alone, given
gcd(product of live values in a slice, product of the divisor range) = 1 for every slice. The
2026-11-12 pricing measured what computing those gcds costs. It did not check that they come out 1.

The gcd over a slice is 1 exactly when no live value in it is divisible by any divisor in the
range. A value of the window is live when no prime up to 32768 divides it. Any composite n near
1e14 has a prime factor at most 1e7, so a live composite is divisible by some prime in
(32768, 1e7], which is the divisor range. So:

    every gcd is 1   <=>   every live value in the window is prime.

This counts the live composites directly, by sieving the window twice: once by the primes up to
32768, which is what "live" means, and once by all the primes up to 1e7, which leaves the primes.
The difference is the number of live composites, and every one of them is a value that makes some
slice's gcd bigger than 1.
"""

import numpy as np

LO = 100000000000001
W = 4194304          # bits in a window, one per integer coprime to 6
SPAN = 3 * W         # integers covered
SMALL = 32768        # the sieve the window arrives already carrying
BIG = 10**7          # the largest base divisor, and sqrt of the numbers here


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p :: p] = False
    return np.flatnonzero(s)


def mark(alive, ps):
    """Clear every multiple of every prime in ps that lands in [LO, LO+SPAN)."""
    for p in ps:
        p = int(p)
        start = ((LO + p - 1) // p) * p
        if start < LO + SPAN:
            alive[start - LO :: p] = False


ps = primes_upto(BIG)
print(f"base primes up to {BIG}: {len(ps)}")

# The window holds the integers coprime to 6, which is where the bits come from.
idx = np.arange(SPAN, dtype=np.int64)
n = LO + idx
coprime6 = ((n % 2) != 0) & ((n % 3) != 0)
print(f"window {LO} .. {LO + SPAN}, integers coprime to 6: {coprime6.sum()} (bits: {W})")

small = ps[ps <= SMALL]
alive = coprime6.copy()
mark(alive, small[small > 3])
live = int(alive.sum())
print(f"live after sieving by the {len(small)} primes up to {SMALL}: {live}")

big = ps[(ps > SMALL) & (ps <= BIG)]
mark(alive, big)
prime = int(alive.sum())
print(f"still live after the {len(big)} divisors in ({SMALL}, {BIG}]: {prime}")

print()
print(f"live composites in the window: {live - prime}")
print(f"  these are the values that make a slice's gcd exceed 1")
print(f"  fraction of live values that are composite: {(live - prime) / live:.3f}")

# Per slice, since the certificate states one gcd per 65536-bit slice.
slices = W // 65536
bit_of = np.cumsum(coprime6) - 1
comp_bits = bit_of[coprime6 & ~alive]
per_slice = np.bincount(comp_bits // 65536, minlength=slices)
print()
print(f"slices: {slices}; slices whose gcd would be 1 (no live composite): {(per_slice == 0).sum()}")
print(f"live composites per slice: min {per_slice.min()}, max {per_slice.max()}")
