"""Check the record against Mertens' second theorem, as an independent sanity test.

The enclosure came from four Lean range theorems added together by hand, so a transcription
error in any of the four As would move the answer without anything catching it. Mertens says the
sum over primes up to x is log log x plus the Meissel-Mertens constant, with Rosser and
Schoenfeld bounding the difference by 1/(10 log^2 x) + 4/(15 log^3 x) for x at least 286. That is
far too weak to confirm ten decimal places, but it is more than strong enough to catch a digit
in the wrong place.
"""

from fractions import Fraction
import math

N = 20635312384
A = 259575801177711258249
C = 6594249936
S = 10 ** 20
M = 0.2614972128476427837554268386086958590516  # Meissel-Mertens

lo = float(Fraction(A, S) + Fraction(5, 6))
hi = float(Fraction(A + C, S) + Fraction(5, 6))

lx = math.log(N)
approx = math.log(lx) + M
bound = 1 / (10 * lx ** 2) + 4 / (15 * lx ** 3)

print(f"N = {N}")
print(f"  kernel-checked   {lo:.12f} to {hi:.12f}")
print(f"  Mertens estimate {approx:.12f}")
print(f"  Rosser-Schoenfeld allows +/- {bound:.3e}")
print(f"  difference from the enclosure's lower end {approx - lo:+.3e}")
print(f"  inside the bound: {abs(approx - lo) < bound}")
