"""Where should the skip set's threshold sit?

`run_segment_skip a W fuel len thr` marks every divisor up to `thr` unconditionally and tests the
rest, skipping those that strike nothing still live. `thr` was taken as 32768 from an old note and
has never been varied. Raising it marks more divisors outright but leaves fewer live values for
the rest to strike, so more of them can be skipped; the total marked is what matters.

The sweep does not need one pass per threshold. For a position n in the window write spf(n) for its
smallest prime factor. A multiple n of p is already dead before p is applied exactly when
spf(n) <= thr, so, writing M(p) for the largest spf over p's multiples in the window,

    p is skippable at thr   <=>   M(p) <= thr.

So M is computed once and every threshold is read off it.

Counts only. What a marked divisor costs depends on its band and is not modelled here.
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

# spf over the window. Writing the primes in descending order leaves the smallest one that hits a
# position as the value that survives.
spf = np.zeros(SPAN, dtype=np.int64)
for p in ps[::-1]:
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        spf[start - LO :: p] = p

n = LO + np.arange(SPAN, dtype=np.int64)
coprime6 = ((n % 2) != 0) & ((n % 3) != 0)
# A position with no factor up to 1e7 is prime, and nothing ever kills it.
spf[coprime6 & (spf == 0)] = np.iinfo(np.int64).max

big = ps[ps > 3]
M = np.zeros(len(big), dtype=np.int64)
for j, p in enumerate(big):
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        sl = spf[start - LO :: p]
        sl = sl[coprime6[start - LO :: p]]
        M[j] = sl.max() if sl.size else 0

bands = [
    ("masked small", big * 8 <= WM1 * 3),
    ("eight-strike", (big * 4 <= WM1 * 3) & (big * 8 > WM1 * 3)),
    ("four-strike", (big * 2 <= WM1 * 3) & (big * 4 > WM1 * 3)),
    ("wide", big * 2 > WM1 * 3),
]

print(f"{'thr':>8} {'prefix':>8} {'tested':>8} {'skipped':>8} {'marked':>8} {'marked/all':>11}")
total = len(big)
for thr in [4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288]:
    prefix = int((big <= thr).sum())
    tested = total - prefix
    skipped = int(((big > thr) & (M <= thr)).sum())
    marked = total - skipped
    print(f"{thr:8} {prefix:8} {tested:8} {skipped:8} {marked:8} {marked / total:11.3f}")

print()
print("marked divisors by band, per threshold")
hdr = "     thr " + " ".join(f"{name:>14}" for name, _ in bands)
print(hdr)
for thr in [8192, 32768, 131072, 524288]:
    skip = (big > thr) & (M <= thr)
    row = " ".join(f"{int((sel & ~skip).sum()):14}" for _, sel in bands)
    print(f"{thr:8} {row}")
