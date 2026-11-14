"""How many records would a record-driven certificate add to what the route already handles?

The gcd products were unaffordable because they inspect the window a bit at a time, about 8 million
`testBitK` calls against a multi-megabit literal. The route is affordable because it never inspects:
`stripeUpToK` walks the records it is given. So the certificate has to be stated over records too.

Before anyone writes the kernel side, the question worth answering by counting is how many records
that is, against the number the route already carries. Both sides are record counts, so they are
comparable as counts; what a record costs in each setting is not claimed here and differs between
assembling and multiplying.

  route today        one record per strike, over the divisors the sweep still marks
  certificate        one record per live value of the finished window, plus one per skipped divisor
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

spf = np.zeros(SPAN, dtype=np.int64)
for p in ps[::-1]:
    p = int(p)
    start = ((LO + p - 1) // p) * p
    if start < LO + SPAN:
        spf[start - LO :: p] = p

n = LO + np.arange(SPAN, dtype=np.int64)
coprime6 = ((n % 2) != 0) & ((n % 3) != 0)
smallest = spf[coprime6]

# Struck divisors are the distinct smallest prime factors; the rest are skipped by the sweep.
struck = np.isin(big, np.unique(smallest[(smallest > 3) & (smallest <= BIG)]))
wide = big > WM1 // 2
marked = struck | ~wide          # the sweep marks every non-wide divisor regardless
skipped = ~marked

# Strike records per divisor: two per 6p of span, plus the partial one.
recs = 2 * (SPAN // (6 * big.astype(np.int64)) + 1)
route_now = int(recs[marked].sum())

# The finished window's live values are the primes in it.
live_final = int((smallest > BIG).sum() + (smallest == 0).sum())
cert = live_final + int(skipped.sum())

print(f"divisors marked by the sweep:       {int(marked.sum())}")
print(f"divisors skipped by the sweep:      {int(skipped.sum())}")
print(f"live values of the finished window: {live_final}")
print()
print(f"records the route carries after the sweep: {route_now}")
print(f"records a certificate would add:           {cert}")
print(f"  live side  {live_final}")
print(f"  skip side  {int(skipped.sum())}")
print(f"ratio: {cert / route_now:.3f} of what the route already handles")
print()
print("Record counts only. Assembling a record and multiplying by one are different operations,")
print("and nothing here says what either costs; that needs the kernel side built and measured.")
