"""How many (divisor, position) records does a strike pass have to handle?

The separate marking pass has to go: it builds a window-wide mask for each of 664577 divisors and
reaches 40 GB. The replacement tests each divisor's actual strike positions instead, grouped by
65536-bit slice so that a test touches one slice rather than the whole window, which is what
`stripeSort` already does for the marking route.

What that costs is a count rather than a guess: the number of (divisor, position) pairs, and how
they fall across the bands and across the slices. A divisor p has about 3W/p strike positions in a
window of 3W integers, so the small divisors dominate the count while the wide band, which holds
90.5% of the saving, contributes about two each.

Counts only. Nothing here says what the pass costs in time or memory.
"""

import numpy as np

LO = 100000000000001
W = 4194304
SPAN = 3 * W
WM1 = W - 1
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
big = ps[ps > 3]

# A divisor strikes the bits standing for its multiples that are coprime to 6; of its multiples in
# the window, those are the ones not divisible by 2 or 3, which is a third of them, two per 6p.
mult = SPAN // big.astype(np.int64)
recs = 2 * (SPAN // (6 * big.astype(np.int64)) + 1)

# Band edges exactly as the emitter sets them: it advances `first` while `2 * value first <= wm1`,
# and the other bands likewise compare a multiple of the divisor against `wm1` itself. An earlier
# version of this script compared against `wm1 * 3`, reasoning about integers covered rather than
# reading the code, which put every boundary a factor of three out and mis-attributed the per-band
# figures. The totals never depended on the split, but the band columns did.
bands = [
    ("masked small", big * 8 <= WM1),
    ("eight-strike", (big * 4 <= WM1) & (big * 8 > WM1)),
    ("four-strike", (big * 2 <= WM1) & (big * 4 > WM1)),
    ("wide", big * 2 > WM1),
]

print(f"{'band':16} {'divisors':>9} {'records':>12} {'per divisor':>12}")
total = 0
for name, sel in bands:
    n = int(sel.sum())
    r = int(recs[sel].sum())
    total += r
    print(f"{name:16} {n:9} {r:12} {r / max(n, 1):12.1f}")
print(f"{'all':16} {len(big):9} {total:12} {total / len(big):12.1f}")

print()
print(f"records per slice, if spread evenly over {SLICES}: {total // SLICES}")
print(f"window bits: {W}; records as a fraction of bits: {total / W:.2f}")

# What the marking route would carry afterwards. Skipping a divisor removes its records from the
# route, so this is the count the route is left with, which is a count and not a cost: what those
# records are worth in kernel seconds is for a measurement.
spf = np.zeros(SPAN, dtype=np.int64)
for p in ps[::-1]:
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        spf[start - LO :: p] = p
nwin = LO + np.arange(SPAN, dtype=np.int64)
coprime6 = ((nwin % 2) != 0) & ((nwin % 3) != 0)
smallest = spf[coprime6]
struck = np.isin(big, np.unique(smallest[(smallest > 3) & (smallest <= BIG)]))

print()
print("Do not total the columns below across bands. Only the sorted bands carry one record per")
print("strike; the masked small band builds a mask per divisor instead, and a mask costs what it")
print("costs whether the divisor has 195 strikes or none. So its record column is the strike count")
print("and not the work, and an 'all' row would be adding two different things and would make the")
print("skip look like a tenth of the total when that figure means nothing.")
print()
print(f"{'band':16} {'divisors now':>13} {'if skipped':>12} {'removed':>9} {'records removed':>16}")
for name, sel in bands:
    dn = int(sel.sum())
    da = int((sel & struck).sum())
    rr = int(recs[sel].sum() - recs[sel & struck].sum())
    print(f"{name:16} {dn:13} {da:12} {dn - da:9} {rr:16}")

# The wide band alone, as a candidate for restricting the strike pass to.
wide = big * 2 > WM1
print()
print(f"wide band only: {int(wide.sum())} divisors, {int(recs[wide].sum())} records, "
      f"{recs[wide].sum() / W:.3f} per window bit")
print("A pass restricted to it would leave the other three bands marked unconditionally, giving")
print("up whatever skips they hold; gcd_skippable_by_band.py reports that split on these same")
print("edges, so take the figure from there rather than from a number written in by hand.")
