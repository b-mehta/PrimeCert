"""Count the work in the paper's identity at several heights, before any of it is written.

The identity cuts at y, sets a = pi(y), and expands phi(x, a) by phi(t, b) = phi(t, b-1) -
phi(t/p_b, b-1). Each branch multiplies a squarefree m by p_b, keeping every prime factor of m
above p_b. A branch stops as a SPECIAL leaf when m exceeds y, and a path that reaches b = 1 with
m at most y stops as an ORDINARY leaf, answered by a logarithm.

This enumerates both exactly, for any y, so the cut can be swept rather than fixed at x^(1/3).
It also counts the sieve to x/y that S_2 and the special leaves share, and the pairs in S_2.

Usage: count_leaves.py [X ...]      (default 1e11 1e12 1e13 1e14)
"""

import sys
from bisect import bisect_right
from math import isqrt, log


def sieve(n):
    flags = bytearray([1]) * (n + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p * p :: p] = bytearray(len(flags[p * p :: p]))
    return [i for i in range(n + 1) if flags[i]]


def pi_approx(t):
    """li(t) by its series, used only where t is too large to sieve."""
    if t < 2:
        return 0.0
    lt, term, total = log(t), 1.0, 0.0
    for k in range(1, 60):
        term *= lt / k
        total += term / k
    return 0.5772156649015329 + log(lt) + total


def leaves(y, primes):
    """(ordinary, special) leaf counts for the cut at y.

    Walks squarefree m with every prime factor above p_b, depth first. `j` indexes the smallest
    prime allowed in m, so m's factors are primes[j:] and the branch that created m used p_b with
    b <= j.
    """
    a = bisect_right(primes, y)
    ordinary = special = 0
    stack = [(1, a)]            # (m, index one past the largest b this m may still be cut by)
    while stack:
        m, hi = stack.pop()
        ordinary += 1 if m <= y else 0
        for b in range(hi):
            mp = m * primes[b]
            if mp > y:
                special += 1
            else:
                stack.append((mp, b))
    return a, ordinary, special


def s2_pairs(x, y, primes):
    """Pairs y < p <= q with p*q <= x, and the sieve limit they need."""
    pairs = 0
    for p in primes:
        if p <= y:
            continue
        if p * p > x:
            break
        top = x // p
        pairs += (pi_approx(top) - bisect_right(primes, p) + 1)
    return int(pairs)


def report(x):
    cube = round(x ** (1 / 3))
    limit = max(isqrt(x) + 1, cube + 1)
    primes = sieve(limit)
    print(f"\nx = {x:.3e}")
    print(f"{'y':>12} {'a = pi(y)':>10} {'ordinary':>12} {'special':>14} {'sieve to x/y':>14}")
    for y in (round(x ** 0.25), round(x ** 0.28), cube, round(x ** 0.36), round(x ** 0.4)):
        if y < 10 or y >= limit:
            continue
        a, ordinary, special = leaves(y, primes)
        print(f"{y:>12} {a:>10} {ordinary:>12} {special:>14} {x // y:>14.3e}")
    a, ordinary, special = leaves(cube, primes)
    pairs = s2_pairs(x, cube, primes)
    direct = pi_approx(x)
    print(f"  at y = x^(1/3) = {cube}: S_2 pairs {pairs:.3e}, "
          f"sieve to x^(2/3) = {round(x ** (2/3)):.3e}")
    print(f"  primes summed directly instead: {direct:.3e}")


for arg in sys.argv[1:] or ["1e11", "1e12", "1e13", "1e14"]:
    report(int(float(arg)))
