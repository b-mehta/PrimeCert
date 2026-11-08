"""The emitter call for one window of a run over 1..N.

`fuel_by_window.py` costs the range when each window is sieved only by the divisors it needs. This
turns that into the call to make: for a window index it prints the `run_segment` line, with the
fuel set from the window's own top rather than from the top of the whole range.

A window of `W` wheel positions covers `3 * W` integers, since the wheel keeps two residues in
every six. Window `k` therefore starts at `1 + k * 3 * W` and ends at `(k + 1) * 3 * W`. It is
sound once every prime up to the square root of its top has been crossed off it, so the divisor
bound is that square root and the fuel is the number of wheel positions up to it. The emitter
reads the bound back off the fuel, so passing less fuel states the result at the smaller bound;
`IsSieve.mono` carries one cached sieve down to it.

Soundness also asks for `7 * B <= a`. That holds from window 1 onwards, so window 0, covering
1..12582912, is the only one of the 7947285 windows of 1..10^14 wanting its own treatment.
"""

import math
import sys

W = 4194304
SEG = 3 * W


def index(n: int) -> int:
    """The wheel index of `n`: how many positions coprime to 6 are at or below it."""
    return n // 6 * 2 + (1 if n % 6 >= 1 else 0) + (1 if n % 6 >= 5 else 0)


def window(k: int) -> tuple[int, int, int, int]:
    """The start, top, divisor bound and fuel for window `k`, counting from 0."""
    lo = k * SEG + 1
    top = (k + 1) * SEG
    bound = math.isqrt(top)
    return lo, top, bound, index(bound)


def main() -> None:
    ks = [int(a) for a in sys.argv[1:]] or [0, 1, 1000, 1000000, 7947284]
    full = index(10**7)
    for k in ks:
        lo, top, bound, fuel = window(k)
        share = fuel / full
        print(f"window {k}: covers {lo}..{top}")
        print(f"  divisors to {bound}, fuel {fuel}, which is {share:.4f} of the {full} "
              f"a top-of-range window needs")
        print(f"  run_segment {lo} {W} {fuel} 8192 10000000")


if __name__ == "__main__":
    main()
