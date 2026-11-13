"""Which bands do the skippable divisors fall in?

75% of base divisors strike nothing live, but they are scattered, so a certificate over contiguous
ranges cannot use them. `segLoopK_eq_self_of_blocks` takes the divisor set as a bitmask rather than
a range, so an arbitrary subset works at 64 gcds total, one per slice.

What decides the value is not the count of skippable divisors but which bands they sit in, because
the bands cost very different amounts per divisor. The wide band is 57.6-58.4 s of a window's
149.7-151.0 s of kernel. A divisor there has two strikes in the window and so is far more likely
to strike nothing live than one near 32768, which has hundreds.

Bands are set by how many strikes a divisor has against Wm1 = W-1, in the same terms the emitter
uses: masked small band 8p <= Wm1, eight-strike 4p <= Wm1 < 8p, four-strike 2p <= Wm1 < 4p, wide
Wm1 < 2p.
"""

import numpy as np

LO = 100000000000001
W = 4194304
SPAN = 3 * W
WM1 = W - 1
SMALL = 32768
BIG = 10**7


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p :: p] = False
    return np.flatnonzero(s)


ps = primes_upto(BIG)
n = LO + np.arange(SPAN, dtype=np.int64)
alive = ((n % 2) != 0) & ((n % 3) != 0)

small = ps[ps <= SMALL]
for p in small[small > 3]:
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        alive[start - LO :: p] = False

big = ps[(ps > SMALL) & (ps <= BIG)]
strikes = np.zeros(len(big), dtype=bool)
for j, p in enumerate(big):
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        strikes[j] = alive[start - LO :: p].any()

# A divisor's band. The window covers 3W integers, so p has about 3W/p multiples in it; the
# emitter's bands are stated against Wm1 in bit terms, which is 3p against the span.
bands = [
    ("masked small (8p <= Wm1)", big * 8 <= WM1 * 3),
    ("eight-strike (4p <= Wm1 < 8p)", (big * 4 <= WM1 * 3) & (big * 8 > WM1 * 3)),
    ("four-strike  (2p <= Wm1 < 4p)", (big * 2 <= WM1 * 3) & (big * 4 > WM1 * 3)),
    ("wide         (Wm1 < 2p)", big * 2 > WM1 * 3),
]

print(f"{'band':34} {'divisors':>9} {'skippable':>10} {'fraction':>9}")
for name, sel in bands:
    tot = int(sel.sum())
    if tot == 0:
        continue
    skip = int((sel & ~strikes).sum())
    print(f"{name:34} {tot:9} {skip:10} {skip / tot:9.3f}")

tot = len(big)
skip = int((~strikes).sum())
print(f"{'all':34} {tot:9} {skip:10} {skip / tot:9.3f}")

# The gcd operands, as sizes rather than as a cost: one product over the skippable divisors, and
# one live product per 65536-bit slice.
pskip = big[~strikes]
bits_divisors = float(np.log2(pskip.astype(float)).sum())
live_vals = n[alive]
bits_live = float(np.log2(live_vals.astype(float)).sum())
print()
print(f"product of the {len(pskip)} skippable divisors: {bits_divisors / 8e6:.2f} MB")
print(f"live product over the whole window:        {bits_live / 8e6:.2f} MB")
print(f"live product per 65536-bit slice:          {bits_live / 64 / 8e3:.1f} KB")
