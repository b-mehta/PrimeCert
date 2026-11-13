"""How much of the window does the wide sweep's base actually need marked?

The sweep measured 31% less kernel, with the wide band falling 66 s to 16 s. What is left is an
80 s pass that marks the three lower bands plainly so the sweep has a window to test against. The
sweep itself is cheap; that pass is not.

But the base does not have to be the state after all three lower bands. Testing against a window
with more live bits only makes wide divisors look like strikers, never the reverse, so a shallower
base is still correct and costs only skips. This counts the skips at each depth:

  none        no divisors marked at all
  small       after the masked small band, 8p <= Wm1
  +eight      after that and the eight-strike band
  +four       after that and the four-strike band, which is what the sweep marks today

The divisor counts at each depth say what the pass would cost in mask builds, and the skip counts
say what it would give up. Counts only; what a mask build costs is for a measurement.
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
big = ps[ps > 3]
n = LO + np.arange(SPAN, dtype=np.int64)
coprime6 = ((n % 2) != 0) & ((n % 3) != 0)

# Band edges as the emitter sets them, against wm1 itself.
depths = [
    ("none", 3),
    ("small", WM1 // 8),
    ("+eight", WM1 // 4),
    ("+four", WM1 // 2),
]

wide = big > WM1 // 2
wp = big[wide]
print(f"wide divisors: {len(wp)}")
print()
print(f"{'base depth':12} {'divisors marked':>16} {'wide struck':>12} {'wide skipped':>13}")

for name, bound in depths:
    alive = coprime6.copy()
    lower = big[big <= bound]
    for p in lower:
        p = int(p)
        start = ((LO + p - 1) // p) * p
        if start < LO + SPAN:
            alive[start - LO :: p] = False
    struck = 0
    for p in wp:
        p = int(p)
        start = ((LO + p - 1) // p) * p
        if start < LO + SPAN and alive[start - LO :: p].any():
            struck += 1
    print(f"{name:12} {len(lower):16} {struck:12} {len(wp) - struck:13}")

print()
print("Read the last row against the sweep as built: it marks every divisor up to WM1//2 plainly.")
print("A shallower base trades skips for mask builds, and only a measurement says which wins.")
