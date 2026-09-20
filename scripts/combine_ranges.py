"""Combine the four kernel-checked ranges into one enclosure of the sum of 1/p.

Every range is an enclosure at scale 10^20: A/S at most the sum of the reciprocals of its primes,
and (A + C)/S at least. The wheel omits 2 and 3, so 1/2 + 1/3 is added once at the end. The
arithmetic is checked against the standing record's published digits before being applied to the
new ranges.
"""

from fractions import Fraction

S = 10 ** 20

PIECES = [
    ("primes up to 100000000", 234164189658716328899, 5761453),
    ("100000001 to 1005969664", 11806779523140848021, 45374243),
    ("1005969665 to 10820641024", 10849165638201014977, 3271557120),
    ("10820641025 to 20635312384", 2755666357653066352, 3271557120),
]

CHECK = [
    ("primes up to 100000000", 234164189658716328899, 5761453),
    ("100000001 to 1005969664", 11806779523140848021, 45374243),
    ("1005969665 to 5535817984", 7905464407962382352, 1509949440),
]


def combine(pieces, label):
    a = sum(p[1] for p in pieces)
    c = sum(p[2] for p in pieces)
    lo = Fraction(a, S) + Fraction(5, 6)
    hi = Fraction(a + c, S) + Fraction(5, 6)
    print(f"{label}: A = {a}, C = {c}")
    print(f"  lower {float(lo):.16f}")
    print(f"  upper {float(hi):.16f}")
    print(f"  width {float(hi - lo):.3e}")
    ls, hs = f"{float(lo):.16f}", f"{float(hi):.16f}"
    agree = 0
    for x, y in zip(ls, hs):
        if x != y:
            break
        agree += 1
    print(f"  agreed to {ls[:agree]}")


combine(CHECK, "the record of 2026-09-19, to 5535817984")
print()
combine(PIECES, "the new total, to 20635312384")
