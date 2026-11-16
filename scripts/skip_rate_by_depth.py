"""Does the wide band's skip rate keep rising above 10^16, and how many divisors still strike?

The sweep tests each wide divisor against the base window and marks only those that strike a live
position. At 10^14 that skipped 79.5% of the wide band; at 10^16 it skipped 96.5%. The question
this answers is what the rate and the struck count do at 10^17 and 10^18, because the struck count
is what the record certificate has to carry and the skipped count is what the gcd product covers.

Counts only. What either costs is for a measurement.

`band_skippable.py` answers the same question by holding every prime below the bound in one array,
which is 1 GB of bool plus the index array at 10^18. This walks the bound in chunks instead, so it
runs in the window's own 12.6 MB plus one chunk, and it reports the wide band alone.

  python3 scripts/skip_rate_by_depth.py                      # 10^14 + 1 and 10^16 + 1
  python3 scripts/skip_rate_by_depth.py 100000000000000001   # one depth, bound set to its root
"""

import sys

import numpy as np

W = 4194304
SPAN = 3 * W
WM1 = W - 1
CHUNK = 1 << 23

# The settled run sweeps from the eight-strike band up, not from the wide band, so that is where
# this starts too. Reproducing the run's own counts is the only check this script has.
SWEEP_LO = WM1 // 8 + 1
MAXHITS = SPAN // SWEEP_LO + 2
# And it tests against the shallow base, built only to Wm1/128. A shallower base leaves more
# positions live, so more divisors strike one; using the full small band here understates how
# many the run has to mark.
BASE_K = 128


def small_primes(n):
    """Every prime up to n, by a plain sieve. Only ever called with n = isqrt(bound)."""
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p * p :: p] = False
    return np.flatnonzero(s)


def build_base(lo):
    """The window the sweep tests against: coprime to 6, with the base's own divisors removed.

    That is `BASE_K * p <= Wm1`, the divisors the run marks before the sweep begins, and the
    sweep then tests everything above them.
    """
    n = lo + np.arange(SPAN, dtype=np.int64)
    base = ((n % 2) != 0) & ((n % 3) != 0)
    for p in small_primes(WM1 // BASE_K):
        p = int(p)
        if p <= 3:
            continue
        start = ((lo + p - 1) // p) * p
        if start < lo + SPAN:
            base[start - lo :: p] = False
    return base


def sweep_chunk(ps, lo, base):
    """How many of these divisors strike a live position in the base, and how many do not.

    One column per possible multiple, so the whole chunk is tested at once rather than divisor by
    divisor. A column past the end of the window is masked off, not read.
    """
    if ps.size == 0:
        return 0, 0
    p64 = ps.astype(np.int64)
    first = ((lo + p64 - 1) // p64) * p64 - lo
    hit = np.zeros(ps.size, dtype=bool)
    for k in range(MAXHITS):
        off = first + k * p64
        live = off < SPAN
        if not live.any():
            break
        idx = np.where(live, off, 0)
        hit |= live & base[idx]
    return int(np.count_nonzero(hit)), int(ps.size - np.count_nonzero(hit))


def report(lo, bound):
    base = build_base(lo)
    roots = small_primes(int(bound**0.5) + 1)
    struck = 0
    skipped = 0
    start = SWEEP_LO
    while start <= bound:
        stop = min(bound, start + CHUNK - 1)
        seg = np.ones(stop - start + 1, dtype=bool)
        for p in roots:
            p = int(p)
            begin = max(p * p, ((start + p - 1) // p) * p)
            if begin <= stop:
                seg[begin - start :: p] = False
        ps = np.flatnonzero(seg) + start
        a, b = sweep_chunk(ps, lo, base)
        struck += a
        skipped += b
        start = stop + 1
    total = struck + skipped
    pct = 100.0 * skipped / total if total else 0.0
    live = int(np.count_nonzero(base))
    print(
        f"{lo:>21} {bound:>12} {total:>12} {struck:>10} {skipped:>12} {pct:10.2f}%"
        f" {live:>10}"
    )


def main():
    if len(sys.argv) > 1:
        depths = [int(a) for a in sys.argv[1:]]
    else:
        depths = [10**14 + 1, 10**16 + 1]
    print(
        f"{'window start':>21} {'bound':>12} {'swept':>12} {'struck':>10}"
        f" {'skipped':>12} {'skipped %':>11} {'base live':>10}"
    )
    for lo in depths:
        bound = int(lo**0.5) + 1
        report(lo, bound)


if __name__ == "__main__":
    main()
