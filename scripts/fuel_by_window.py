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

# Measured seconds for one window at batch 8192, two windows sharing a runner, which is the shape
# a real run uses. The band split is taken from the one-file run 42389213113 in these proportions:
# small divisors, the two middle bands, and the widest band.
#
# The non-kernel remainder was once carried here as a constant, on the reasoning that elaboration
# does not depend on the divisor count. Two paired runs say otherwise. A window given the divisors
# window 1000 of 1..10^14 needs, a hundredth of the top window's, costs 0.0815 of the top
# (run 42785072832: 183/162/159 s of group wall against 15/12/14), where a constant remainder
# predicts 0.260; and a window at half the divisors costs 0.762 (run 42777596039: 226/225/229
# against 172/172/174). So the remainder scales with the work and is distributed across the bands
# rather than added on top.
_SPLIT = {"small": 53.96, "eight": 42.69 / 2, "four": 42.69 / 2, "wide": 69.99}
_PAIRED = 149.0 / 2              # seconds of runner time one window takes, two to a runner
_SCALE = _PAIRED / sum(_SPLIT.values())
COST = {k: v * _SCALE for k, v in _SPLIT.items()}
OTHER = 0.0

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


def range_cost(n: int) -> tuple[int, float, float]:
    """Windows, mean seconds of runner time per window, and total runner-years, for 1..n."""
    windows = max(1, n // SEG)
    samples = 20000
    acc = 0.0
    for k in range(samples):
        x = (k + 0.5) / samples * n
        acc += window_cost(int(x ** 0.5))
    mean = acc / samples
    return windows, mean, windows * mean / 3600 / 24 / 365


def main() -> None:
    top = window_cost(FULL_B)
    print(f"primes per band: {PI}")
    print(f"one window at the top of 1..1e14: {top:.1f} s of runner time")
    print()
    # A GitHub job runs at most six hours and takes two windows at once, so it carries
    # 2 * 21600 / mean windows.
    print("  N        windows      s/window   runner-years   six-hour jobs")
    for e in (11, 12, 13, 14):
        n = 10 ** e
        windows, mean, years = range_cost(n)
        jobs = windows * mean / 2 / 21600
        print(f"  1e{e:<6} {windows:>10}   {mean:>8.1f}   {years:>12.2f}   {jobs:>13.0f}")


if __name__ == "__main__":
    main()
