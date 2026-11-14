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
# THE ANCHOR BELOW PREDATES TWO MEASURED CHANGES AND SO OVERSTATES THE COST.
# It was taken before the emitter reached the next window through a byte array, and before the
# allocator settings went into the run scripts. Measured on one quiet 32 vCPU box, alternating
# arms: the byte array took a window from 110.5/112.9/112.0 to 87.7/85.7/85.6 processor seconds,
# and the settings took 84.7-86.1 to 75.8-76.5. Together about 0.68 of what this anchor assumes.
# The figures this file prints are therefore an upper bound. They are left as they are rather than
# scaled, because the anchor and the newer measurements come from different machines and the whole
# point of the anchor is that it was measured in the shape a real run uses. Re-anchor by repeating
# that paired measurement on the machine a run will actually use.
# RE-ANCHORED 2026-11-12 on a window with the divisors a run actually needs.
#
# Everything above describes the old anchor and is kept because its reasoning still holds. The
# numbers below replace it. `ZZ9_FullWindow` is one window of 4194304 wheel positions from
# 10^14 + 1 sieved by every prime to 10^7, which is what the topmost window needs, measured on a
# fresh c7i.8xlarge with `run.sh 3` after a 120 s settle, three rounds within 0.6%:
#
#     kernel 156.7-157.7 s, processor 173.0-174.0 s, peak 2.61 GB, 1469 batch lemmas
#     wide band 61.6-61.9 s | sorted bands 47.6-48.1 s | masked small band 45.2-45.5 s
#
# Every earlier SegTune case used divisors to about 10^6, a tenth of these, which is enough to
# compare two routes and not enough to apportion a run: the widest band holds almost all the
# divisors and is barely represented at a tenth. It is the largest share here, at 39% of kernel.
#
# The split below is the measured one. `eight` and `four` share the sorted row because `run.sh`
# reports them together; they are split evenly, which is the one guess left in this model.
#
# **Absolute seconds are host-dependent, by more than any change measured here.** Four fresh
# c7i.8xlarge boxes ran this same window at **161.6-162.5, 173.0-174.0, 177.5-184.1 and 226 s** of
# processor. The 226 was checked and is not explained by flags: `-Dtrace.profiler=true
# -Dtrace.profiler.threshold=0`, which `run.sh` adds, cost nothing measurable (178.1/177.7 against
# 177.5/184.1, alternated A B B A on one box). Even setting it aside the spread is about 7%.
# So **compare arms only within one job on one box**, and read the figure below as a round number
# with a 160-185 range behind it, not as a measurement.
#
# The band split is from the 173-174 box. A split from a faster box would scale down together, so
# the proportions carry even though the seconds do not.
_SPLIT = {"small": 45.35, "eight": 47.85 / 2, "four": 47.85 / 2, "wide": 61.75}
_PAIRED = 174.0                  # processor seconds for one window alone; 161-185 across hosts
# NOT CHANGED BY THE 2026-11-13 SWEEP, DELIBERATELY. The wide-band sweep (`ZZV_WideSweepNoCheck`)
# beat this route same-box on all three figures: kernel 112.1-113.4 s against 164.9-166.6, processor
# 150.4-152.2 against 181.3-183.3, peak 2.46 GB against 2.61. On processor that is 0.83 of the
# anchor, which would carry straight into the job counts below.
#
# The anchor stays at the production route because **the sweep proves nothing about the 435226
# divisors it skips**, and the certificate that would make it sound has no affordable shape yet.
# Projecting a run off an unsound route would state a reachable N that is not reachable. When the
# certificate lands, re-anchor by measuring the sound arm rather than by scaling this by 0.83: the
# certificate's own cost belongs in the number and is not yet known.
#
# Tonight's control runs also bracket this anchor across three boxes — 163.8-165.7, 170.1-170.9 and
# 179.5-183.3 s of processor for the same file — so the 161-185 range above still holds.
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


# How many windows a runner carries at once. This is set by peak memory, not by cores, and the
# peak depends on a flag: with Lean's asynchronous kernel checking a window peaked at 4.85 GB, and
# with it off at 1.64 GB for the same processor seconds (measured alternated on a quiet box).
# `run.sh` turns it off.
#
# Measured 2026-11-12 on a fresh c7i.8xlarge, copies of `ZZ9_FullWindow` run together in batches
# of 1, 4, 8, 8, 4, 1 with a 120 s settle:
#
#     copies | per-process max RSS | machine used peak | user s per copy
#        1   |      2.58 GB        |     3.10 GB       |   225.2-225.9
#        4   |      2.55 GB        |     8.56-8.59 GB  |   235.7-240.3
#        8   |      2.54-2.57 GB   |    15.86-15.91 GB |   256.0-260.7
#
# **The peak per window does not climb with concurrency**, which was the open question. The machine
# total grows by about 1.83 GB a copy, not 2.55, because the shared oleans are mapped once; the
# fixed part is about 1.3 GB. So copies fitting in `R` gigabytes is `(R - 1.3) / 1.83`, which is
# six on a 14 GB runner and core-bound rather than memory-bound on a 61 GB box.
#
# Not modelled here: CPU per copy rises with concurrency, 6% at four and 15% at eight, so the
# figures below are optimistic by roughly that much at those packings. Beyond eight it is unmeasured.
# Both constants are **mode 28's**, which is what `run_segment` emits. They do not transfer to
# another route: a route with a different per-window peak has its own marginal, and that marginal
# is what decides packing, not the peak of one window measured alone. Comparing two routes on
# throughput therefore needs a concurrency run of each, not one of them and a ratio.
RUNNER_GB = 14.0
WINDOWS_PER_RUNNER = int((RUNNER_GB - 1.3) / 1.83)

# The anchor above is now a current measurement rather than a historical one: it was taken after
# the byte-array route, the allocator settings, the operand order, clamped marking and the banded
# route had all landed. So there is nothing left to scale it by, and anything that lands from here
# re-anchors rather than multiplies.
SPEEDUP = 1.0


def main() -> None:
    top = window_cost(FULL_B)
    print(f"primes per band: {PI}")
    print(f"one window at the top of 1..1e14: {top:.1f} processor seconds "
          f"(measured 2026-11-12; hosts vary 161-185)")
    print(f"windows a {RUNNER_GB:.0f} GB runner holds: {WINDOWS_PER_RUNNER} "
          f"(measured: 1.83 GB a copy over a 1.3 GB fixed part)")
    print()
    print("  N        windows      s/window   runner-years   six-hour jobs   at two a runner")
    for e in (11, 12, 13, 14):
        n = 10 ** e
        windows, mean, years = range_cost(n)
        was = windows * mean / 2 / 21600
        now = windows * mean * SPEEDUP / WINDOWS_PER_RUNNER / 21600
        print(f"  1e{e:<6} {windows:>10}   {mean:>8.1f}   {years * SPEEDUP:>12.2f}   "
              f"{now:>13.0f}   {was:>19.0f}")


if __name__ == "__main__":
    main()
