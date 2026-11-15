"""How much of each band would the sweep skip, if it were extended down to it?

The sweep tests only the wide band, `Wm1 < 2p`, and marks the three lower bands plainly. That
split was chosen because the wide band holds most of the skips, but the three lower bands have
never been counted separately against the same base.

The test is sound for any band: a divisor that strikes nothing live in the base strikes nothing in
the finished window either, because marking only ever clears bits. So extending the sweep down a
band needs no new argument, only a reason — and the reason would be skips it buys against mask
builds it still has to do to find them.

One thing worth knowing before reading the output. The band edges are set by `Wm1`, the window
width, not by the divisor bound, so the three lower bands hold the *same primes* at every depth.
Only the wide band grows as the bound does. What can still move with depth is which multiples
land in this particular window, which is why both depths are worth counting rather than one.

  python3 scripts/band_skippable.py                       # 10^14 + 1, divisors to 10^7
  python3 scripts/band_skippable.py 1000000000000001 31700000
"""

import sys

import numpy as np

LO = int(sys.argv[1]) if len(sys.argv) > 1 else 100000000000001
BIG = int(sys.argv[2]) if len(sys.argv) > 2 else 10**7
W = 4194304
SPAN = 3 * W
WM1 = W - 1


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

# The base the sweep tests against: the masked small band alone, `8p <= Wm1`.
base = coprime6.copy()
for p in big[big <= WM1 // 8]:
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        base[start - LO :: p] = False

bands = [
    ("small  8p<=Wm1", big[big <= WM1 // 8]),
    ("eight  4p<=Wm1", big[(big > WM1 // 8) & (big <= WM1 // 4)]),
    ("four   2p<=Wm1", big[(big > WM1 // 4) & (big <= WM1 // 2)]),
    ("wide   Wm1<2p ", big[big > WM1 // 2]),
]

print(f"window start {LO}, divisors to {BIG}")
print()
print(
    f"{'band':16} {'divisors':>10} {'strike':>9} {'skippable':>10} {'skippable %':>12}"
    f" {'records saved':>14}"
)

for name, members in bands:
    struck = 0
    saved = 0
    for p in members:
        p = int(p)
        start = ((LO + p - 1) // p) * p
        hits = int(np.count_nonzero(coprime6[start - LO :: p])) if start < LO + SPAN else 0
        if start < LO + SPAN and base[start - LO :: p].any():
            struck += 1
        else:
            # A divisor the sweep drops costs the marking one record per position its mask
            # covers, not one per divisor. That is why a band's worth is not its divisor count:
            # the eight-strike band's members each cover up to eight positions where the
            # four-strike band's cover up to four.
            saved += hits
    skip = len(members) - struck
    pct = (100.0 * skip / len(members)) if len(members) else 0.0
    print(f"{name:16} {len(members):10} {struck:9} {skip:10} {pct:11.1f}% {saved:14}")

print()
print("The small band is tested against a base that already includes it, so its own row says")
print("what it would skip if the base were built without it; it is not what the sweep does.")
print("Counts only. What a mask build costs against what a skip saves is for a measurement.")
