"""What sieving 1..10^14 costs when each window gets only the divisors it needs.

A window ending at T is sound once every prime up to sqrt(T) has been crossed off it, so a window
low in the range needs far fewer divisors than one at the top. Today every window is given
divisors to 10^7, which is sqrt(10^14) and is what only the topmost window needs.

Band thresholds come from the emitter's own conditions on a divisor p against Wm1 = W - 1:
small 8p <= Wm1, eight 4p <= Wm1 < 8p, four 2p <= Wm1 < 4p, wide Wm1 < 2p. Band costs are the
measured per-segment kernel seconds at batch 8192 plus the non-kernel remainder, and a band only
partly reached is charged in proportion to the primes of it that are present.
"""

def _sieve(n: int) -> list[int]:
    """Running count of primes up to each index, by a plain sieve."""
    flags = bytearray([1]) * (n + 1)
    flags[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if flags[i]:
            flags[i * i :: i] = bytearray(len(flags[i * i :: i]))
        i += 1
    counts = [0] * (n + 1)
    run = 0
    for k in range(n + 1):
        run += flags[k]
        counts[k] = run
    return counts


_COUNTS: list[int] = []


def primepi(x: float) -> int:
    k = int(x)
    if k < 0:
        return 0
    return _COUNTS[min(k, len(_COUNTS) - 1)]

W = 4194304
WM1 = W - 1
SEG = 3 * W                      # integers one window covers
N = 10**14
FULL_B = 10**7                   # divisors the top window needs

# Measured seconds for one segment at batch 8192, one file (run 35807524908 and the elaboration
# split from run 42317946181).
COST = {"small": 36.3, "eight": 65.0 / 2, "four": 65.0 / 2, "wide": 76.3}
OTHER = 38.0                     # non-kernel elaboration, independent of the divisor count

EDGES = {
    "small": (2, WM1 // 8),
    "eight": (WM1 // 8, WM1 // 4),
    "four": (WM1 // 4, WM1 // 2),
    "wide": (WM1 // 2, FULL_B),
}

_COUNTS = _sieve(FULL_B)

PI = {name: int(primepi(hi)) - int(primepi(lo)) for name, (lo, hi) in EDGES.items()}


def window_cost(bound: int) -> float:
    """Seconds for one window sieved by every prime up to `bound`."""
    total = OTHER
    for name, (lo, hi) in EDGES.items():
        if bound <= lo:
            continue
        present = int(primepi(min(bound, hi))) - int(primepi(lo))
        total += COST[name] * present / PI[name]
    return total


def main() -> None:
    top = window_cost(FULL_B)
    print(f"primes per band: {PI}")
    print(f"a window at the top of the range: {top:.1f} s")

    # Sample windows uniformly across the range and average; the cost only depends on sqrt of the
    # window's top, so sampling the window index is sampling the range.
    windows = N // SEG
    samples = 20000
    acc = 0.0
    for k in range(samples):
        x = (k + 0.5) / samples * N
        acc += window_cost(int(x ** 0.5))
    mean = acc / samples
    print(f"mean over every window of 1..1e14: {mean:.1f} s")
    print(f"ratio mean/top: {mean / top:.4f}")
    print(f"windows in 1..1e14: {windows}")

    years = windows * top / 2 / 3600 / 24 / 365
    print(f"\nat the top rate everywhere, two windows a runner: {years:.1f} runner-years")
    print(f"at the per-window rate:                           "
          f"{windows * mean / 2 / 3600 / 24 / 365:.1f} runner-years")


if __name__ == "__main__":
    main()
