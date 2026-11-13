"""What the skip set comes to when live is taken in the loop's own order.

`segLoopHits` marks divisors in increasing order and records which of them cleared a bit, so a
divisor p is marked exactly when some value of the window still live at p's turn is a multiple of
p. Everything below p has already been applied, so such a value exists exactly when p is the
smallest prime factor of some value in the window:

    p is marked   <=>   p = spf(n) for some n in the window coprime to 6.

So the marked set is the set of distinct smallest prime factors occurring in the window, and the
count follows from one spf pass with no marking simulated at all.

This is a prediction to check the emitter against, not a timing. If `run_segment_skip` at thr 0
reports a different marked count on this window, one of the two is wrong.
"""

import numpy as np

LO = 100000000000001
W = 4194304
SPAN = 3 * W
WM1 = W - 1
BIG = 10**7


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p :: p] = False
    return np.flatnonzero(s)


ps = primes_upto(BIG)

spf = np.zeros(SPAN, dtype=np.int64)
for p in ps[::-1]:
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        spf[start - LO :: p] = p

n = LO + np.arange(SPAN, dtype=np.int64)
coprime6 = ((n % 2) != 0) & ((n % 3) != 0)

# The divisors of the base sieve are those above 3; 2 and 3 are the wheel.
smallest = spf[coprime6]
marked_vals = np.unique(smallest[(smallest > 3) & (smallest <= BIG)])
total = int(((ps > 3) & (ps <= BIG)).sum())

print(f"base divisors in (3, {BIG}]: {total}")
print(f"marked, live taken in order: {len(marked_vals)}  ({len(marked_vals) / total:.3f})")
print(f"skipped:                     {total - len(marked_vals)}  "
      f"({1 - len(marked_vals) / total:.3f})")

bands = [
    ("masked small", lambda p: p * 8 <= WM1 * 3),
    ("eight-strike", lambda p: (p * 4 <= WM1 * 3) & (p * 8 > WM1 * 3)),
    ("four-strike", lambda p: (p * 2 <= WM1 * 3) & (p * 4 > WM1 * 3)),
    ("wide", lambda p: p * 2 > WM1 * 3),
]
big = ps[(ps > 3) & (ps <= BIG)]
is_marked = np.isin(big, marked_vals)
print()
print(f"{'band':16} {'divisors':>9} {'marked':>9} {'skipped':>9} {'skip frac':>10}")
for name, sel in bands:
    m = sel(big)
    tot = int(m.sum())
    mk = int((m & is_marked).sum())
    print(f"{name:16} {tot:9} {mk:9} {tot - mk:9} {1 - mk / tot:10.3f}")

# The largest divisor that is ever a smallest prime factor here: above it nothing is marked, since
# n would need two factors that large.
print()
print(f"largest divisor that is some value's smallest prime factor: {int(marked_vals.max())}")
print(f"divisors above it, all skipped: {int((big > marked_vals.max()).sum())}")
