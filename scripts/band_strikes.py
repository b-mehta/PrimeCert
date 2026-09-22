"""Count, for one segment at the settled configuration, how many strikes each band places.

The bands are the ones `run_segment_variant` dispatches on, in terms of the divisor p and the
window's last offset Wm1:

  small        8p <= Wm1            a periodic mask built by doubling covers every strike at once
  eight    4p <= Wm1 <  8p          up to eight strikes, sorted into records
  four     2p <= Wm1 <  4p          up to four
  wide           Wm1 <  2p          up to two

Strike positions come from the same arithmetic the Lean twin uses: a divisor p strikes the two
progressions seeded at index(5p) and index(7p), with stride 2p in wheel positions.
"""

W = 4194304
Wm1 = W - 1
A = 100000000000001          # the window start used by every case file
BOUND = 10000000             # divisors up to 10^7, which is what 10^14 needs


def index(q: int) -> int:
    return (q - 1) // 3


def value(k: int) -> int:
    return (k * 3 + 1) + k % 2


def first_loc(a: int, lo: int, m: int) -> int:
    return (a + m - lo % m) % m


def primes_upto(n: int) -> bytearray:
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
        i += 1
    return sieve


def main() -> None:
    lo = index(A)
    sieve = primes_upto(BOUND)
    bands = {"small": [0, 0], "eight": [0, 0], "four": [0, 0], "wide": [0, 0]}

    # Walk the same wheel positions the segment walks, 1 .. fuel.
    k = 1
    while True:
        p = value(k)
        if p > BOUND:
            break
        if sieve[p]:
            d = 2 * p
            strikes = 0
            for seed in (index(p * 5), index(p * 7)):
                x = first_loc(seed, lo, d)
                while x <= Wm1:
                    strikes += 1
                    x += d
            if 8 * p <= Wm1:
                band = "small"
            elif 4 * p <= Wm1:
                band = "eight"
            elif 2 * p <= Wm1:
                band = "four"
            else:
                band = "wide"
            bands[band][0] += 1
            bands[band][1] += strikes
        k += 1

    # Kernel seconds per band, means over three rounds of run 35610941156 at fuel 3333332.
    # `run.sh` reports the small divisors under "batch lemmas", the four- and eight-strike bands
    # together under "sorted batch lemmas", and the wide band under "wide band lemmas".
    measured = {"small": 27.9, "eight+four": 49.1, "wide": 45.6}

    tot_p = sum(v[0] for v in bands.values())
    tot_s = sum(v[1] for v in bands.values())
    print(f"{'band':>12} {'primes':>10} {'strikes':>12} {'share':>8} {'kernel s':>9} {'us/strike':>10}")
    for name in ("small", "eight", "four", "wide"):
        n, s = bands[name]
        print(f"{name:>12} {n:>10} {s:>12} {100*s/tot_s:>7.2f}% {'':>9} {'':>10}")
    print()
    mid = bands["eight"][1] + bands["four"][1]
    for name, strikes in (("small", bands["small"][1]), ("eight+four", mid), ("wide", bands["wide"][1])):
        secs = measured[name]
        print(f"{name:>12} {'':>10} {strikes:>12} {100*strikes/tot_s:>7.2f}% {secs:>9.1f} "
              f"{1e6*secs/strikes:>10.2f}")
    print()
    print(f"total primes {tot_p}, total strikes {tot_s}, kernel {sum(measured.values()):.1f} s")
    big = mid + bands["wide"][1]
    print(f"large-prime bands: {100*big/tot_s:.2f}% of strikes, "
          f"{100*(measured['eight+four']+measured['wide'])/sum(measured.values()):.2f}% of kernel")


if __name__ == "__main__":
    main()
