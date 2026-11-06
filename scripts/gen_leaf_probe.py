"""Emit kernel checks that price one special leaf of the paper's identity.

A special leaf asks for the sum of 1/i over the i in a prefix of an interval whose least prime
factor exceeds the b-th prime. Sieving the interval by the first b primes leaves exactly those i,
so the leaf is `sumB (recipAtW w lo S) 0 len 1` over that window: the same fold the production
path runs over primes, with a window sieved by b primes rather than by all of them.

Each emitted theorem is one leaf. Varying b and the prefix length says how the cost moves with
each, which is what the identity's 1.16e7 leaves at x = 1e14 need priced.

Each pair of parameters lands in its own file, so a file's wall divided by the leaves it holds
is the cost of one leaf at those parameters.

Usage: gen_leaf_probe.py OUT_DIR START_POSITION
"""

import sys
from math import isqrt

sys.set_int_max_str_digits(100000)   # window literals reach 65536 bits

SCALE = 10 ** 20
B_VALUES = (16, 64, 256, 1024, 4797)        # primes sieved out; 4797 = pi(1e14^(1/3))
LENGTHS = (1024, 4096, 16384, 65536)        # prefix length, in wheel positions
REPEATS = 2                                  # leaves emitted per (b, length) pair


def value(k: int) -> int:
    return 3 * k + 1 + (k % 2)


def first_primes(n: int) -> list[int]:
    limit = 200
    while True:
        flags = bytearray([1]) * (limit + 1)
        flags[0:2] = b"\x00\x00"
        for p in range(2, isqrt(limit) + 1):
            if flags[p]:
                flags[p * p :: p] = bytearray(len(flags[p * p :: p]))
        ps = [i for i in range(limit + 1) if flags[i]]
        if len(ps) >= n:
            return ps[:n]
        limit *= 2


def index(m: int) -> int:
    """Inverse of `value` on integers coprime to 6."""
    return 2 * ((m - 1) // 6) if m % 6 == 1 else 2 * ((m - 5) // 6) + 1


def survivors(lo: int, length: int, primes: list[int]) -> int:
    """Bitset of positions lo..lo+length-1 whose value has no factor among `primes`.

    Strikes multiples rather than testing each position, so the cost follows the sum of the
    interval length over each prime.
    """
    flags = bytearray([1]) * length
    first, last = value(lo), value(lo + length - 1)
    for p in primes:
        if p in (2, 3):
            continue
        for m in range(((first + p - 1) // p) * p, last + 1, p):
            if m % 6 in (1, 5):
                flags[index(m) - lo] = 0
    w = 0
    for i, f in enumerate(flags):
        if f:
            w |= 1 << i
    return w


def main() -> None:
    out, start = sys.argv[1], int(sys.argv[2])
    ps = first_primes(max(B_VALUES))

    lo = start
    for b in B_VALUES:
        small = ps[:b]
        for length in LENGTHS:
            name = f"L{b}_{length}"
            lines = [
                "/-",
                "Copyright (c) 2026 Bhavik Mehta. All rights reserved.",
                "Released under Apache 2.0 license as described in the file LICENSE.",
                "Authors: Bhavik Mehta",
                "-/",
                "module",
                "",
                "public meta import PrimeCert.Meta.QuickRfl",
                "public import PrimeCert.PrimeHarmonic",
                "",
                f"/-! # {REPEATS} special leaves at {length} positions, first {b} primes removed",
                "",
                "A special leaf of the paper's identity is the sum of 1/i over a prefix of an",
                "interval whose least prime factor exceeds the b-th prime, so sieving the interval",
                "by the first b primes and folding over the survivors is exactly that leaf. The",
                "identity needs 1.16e7 of them at x = 1e14, against 21600 seconds in a runner, so",
                "the cost of one decides whether that route fits.",
                "",
                "Sibling files hold the other values of b and of the prefix length. Nothing here is",
                "proved to be a leaf of anything; the file is for timing.",
                "-/",
                "",
                "set_option linter.style.longLine false",
                "",
                f"namespace PrimeCert.LeafProbe.{name}",
                "",
                "open PrimeCert",
                "",
            ]
            for r in range(REPEATS):
                w = survivors(lo, length, small)
                total = sum(SCALE // value(lo + i) for i in range(length) if (w >> i) & 1)
                lines += [
                    f"/-- {bin(w).count('1')} survivors of {length} positions from {lo}. -/",
                    f"public theorem leaf_{r} : "
                    f"Nat.beq (sumB (recipAtW {w} {lo} {SCALE}) 0 {length} 1) {total} = true := by",
                    "  quickRfl",
                    "",
                ]
                lo += length
            lines += [f"end PrimeCert.LeafProbe.{name}", ""]
            with open(f"{out}/{name}.lean", "w") as f:
                f.write("\n".join(lines))
    print(f"{out}: {len(B_VALUES) * len(LENGTHS)} files of {REPEATS} leaves, "
          f"positions {start} to {lo}")


main()
