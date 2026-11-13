"""Does the wide-band strike test have to run in order?

The measured ceiling is worth finishing (41% less kernel) and the only obstacle is that the strike
set costs a 124 s plain marking pass. The plan is to test only the wide band, 87.5% of the skips in
a tenth of the records. But testing in the loop's own order forces a sequential pass: a wide
divisor's liveness depends on earlier wide divisors having marked.

Testing every wide divisor against one fixed window instead, the state after the other three bands
are marked, makes it a single sweep. That can only ever mark extra divisors, never miss one that
strikes, and marking a divisor whose mask clears nothing is harmless, so it stays correct. What it
costs is skips: a wide p whose only live multiple would have been cleared by a smaller wide divisor
is marked where the ordered test would have skipped it.

This counts that cost exactly. in-order is `p = spf(n)` for some window value, restricted to the
wide band. fixed-window is `p` has a multiple whose smallest prime factor is above the wide
boundary, i.e. no non-wide divisor cleared it first.
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

# The wide boundary, exactly as the emitter sets it: it advances while 2 * value <= wm1.
WIDE = WM1 // 2
big = ps[ps > 3]
wide = big > WIDE
print(f"wide boundary p > {WIDE}; wide divisors {int(wide.sum())} of {len(big)}")

# Both tests are answered by slicing spf at each divisor's multiples, which is about a million
# operations in all. Factoring each live value instead was far too slow and timed out.
#
#   in order      p is marked when some multiple has spf exactly p
#   fixed window  p is marked when some multiple has spf above the wide boundary, meaning no
#                 non-wide divisor cleared it first
wp = big[wide]
in_order = np.zeros(len(wp), dtype=bool)
fixed = np.zeros(len(wp), dtype=bool)
for j, p in enumerate(wp):
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start >= LO + SPAN:
        continue
    sl = spf[start - LO :: p]
    ok = coprime6[start - LO :: p]
    sl = sl[ok]
    if sl.size:
        fixed[j] = bool((sl > WIDE).any())
        in_order[j] = bool((sl == p).any())

nwide = len(wp)
a = int(in_order.sum())
b = int(fixed.sum())
print()
print(f"wide divisors marked, in order:       {a}   skipped {nwide - a}")
print(f"wide divisors marked, fixed window:   {b}   skipped {nwide - b}")
print(f"extra divisors marked by dropping the ordering: {b - a}")
print(f"that is {(b - a) / max(nwide - a, 1):.4f} of the wide skips given up")
