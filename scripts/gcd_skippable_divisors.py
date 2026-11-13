"""How much of the divisor range could the gcd certificate actually skip?

The first check showed the certificate cannot cover the whole divisor range: every slice holds
about 59000 live composites. But `segLoopK_eq_self_of_range` applies to a contiguous range of
divisors, and its hypothesis holds for a range exactly when no divisor in it has a live multiple
anywhere in the window. A divisor with no live multiple builds a mask that clears nothing, so
those are the ones worth skipping.

Two things decide whether this is worth proving:
  - how many divisors strike nothing live, and
  - whether they come in long contiguous runs, since the certificate covers a range and each range
    costs one gcd per slice, 64 gcds.

A run of length L replaces L masks with 64 gcds, so short runs are worse than useless.
"""

import numpy as np

LO = 100000000000001
W = 4194304
SPAN = 3 * W
SMALL = 32768
BIG = 10**7
SLICES = W // 65536


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p :: p] = False
    return np.flatnonzero(s)


ps = primes_upto(BIG)
idx = np.arange(SPAN, dtype=np.int64)
n = LO + idx
alive = ((n % 2) != 0) & ((n % 3) != 0)

small = ps[ps <= SMALL]
for p in small[small > 3]:
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        alive[start - LO :: p] = False

live = alive.copy()          # live = survives the primes up to 32768
big = ps[(ps > SMALL) & (ps <= BIG)]

# For each big divisor, does it have a multiple in the window that is still live?
strikes = np.zeros(len(big), dtype=bool)
for j, p in enumerate(big):
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        strikes[j] = live[start - LO :: p].any()

ns = int(strikes.sum())
print(f"divisors in ({SMALL}, {BIG}]: {len(big)}")
print(f"  strike something live (mask is needed):     {ns}  ({ns / len(big):.3f})")
print(f"  strike nothing live (mask clears nothing):  {len(big) - ns}  ({1 - ns / len(big):.3f})")

# Contiguous runs of skippable divisors, in divisor-index order, which is the order the
# certificate's ranges are taken in.
skip = ~strikes
runs = []
cur = 0
for v in skip:
    if v:
        cur += 1
    elif cur:
        runs.append(cur)
        cur = 0
if cur:
    runs.append(cur)
runs = np.array(runs)

print()
print(f"contiguous skippable runs: {len(runs)}")
print(f"  longest run: {runs.max()}")
print(f"  mean run:    {runs.mean():.2f}")
print(f"  runs of length >= {SLICES} (worth one range's {SLICES} gcds): {(runs >= SLICES).sum()}")
print(f"  divisors inside those runs: {int(runs[runs >= SLICES].sum())}")
print()
masks_saved = int(runs[runs >= SLICES].sum())
gcds_spent = int((runs >= SLICES).sum()) * SLICES
print(f"best case: {masks_saved} masks skipped for {gcds_spent} gcds stated")
