"""Emit kernel checks that price one special leaf walked by gaps.

`gen_leaf_probe.py` answers a leaf with `sumB (recipAtW ...)`, which visits every position in the
prefix and contributes zero at the clear bits, so its cost follows the prefix width and ignores
how many positions survive. This emits the same leaves walked by `gapFoldPosK`, which visits only
the survivors, so the two together say what the prefix width costs and what the survivors cost.

One file per pair of parameters, as in `gen_leaf_probe.py`, so the two can be compared row by row.

Usage: gen_leaf_gap.py OUT_DIR START_POSITION
"""

import sys
from math import isqrt

sys.set_int_max_str_digits(1000000)

FIELD = 8
MASK = (1 << FIELD) - 1
Q = 1 << 32
B_VALUES = (16, 64, 256, 1024, 4797)
LENGTHS = (1024, 4096, 16384, 65536)
REPEATS = 2

if len(sys.argv) > 3:
    REPEATS = int(sys.argv[3])
if len(sys.argv) > 4:
    LENGTHS = (int(sys.argv[4]),)
if len(sys.argv) > 5:
    B_VALUES = (int(sys.argv[5]),)


def value(k: int) -> int:
    return 3 * k + 1 + (k % 2)


def index(m: int) -> int:
    return 2 * ((m - 1) // 6) if m % 6 == 1 else 2 * ((m - 5) // 6) + 1


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


def survivor_positions(lo: int, length: int, primes: list[int]) -> list[int]:
    flags = bytearray([1]) * length
    first, last = value(lo), value(lo + length - 1)
    for p in primes:
        if p in (2, 3):
            continue
        for m in range(((first + p - 1) // p) * p, last + 1, p):
            if m % 6 in (1, 5):
                flags[index(m) - lo] = 0
    return [i for i, f in enumerate(flags) if f]


def main() -> None:
    out, start = sys.argv[1], int(sys.argv[2])
    ps = first_primes(max(B_VALUES))

    lo = start
    for b in B_VALUES:
        small = ps[:b]
        for length in LENGTHS:
            name = f"G{b}_{length}"
            P = 1 << (length + 1)
            PQ = P * Q
            lines = [
                "/-",
                "Copyright (c) 2026 Bhavik Mehta. All rights reserved.",
                "Released under Apache 2.0 license as described in the file LICENSE.",
                "Authors: Bhavik Mehta",
                "-/",
                "module",
                "",
                "public meta import PrimeCert.Meta.QuickRfl",
                "public import PrimeCert.GapFold",
                "",
                f"/-! # {REPEATS} special leaves at {length} positions, walked by gaps",
                "",
                f"The first {b} primes are sieved out of the interval and the survivors are walked",
                "by the gaps between them, so the walk visits the survivors rather than every",
                "position. The sibling files under LeafProbe answer the same leaves by folding over",
                "every position; comparing the two says what the width costs and what the",
                "survivors cost.",
                "",
                "Nothing here is proved to be a leaf of anything; the file is for timing.",
                "-/",
                "",
                "set_option linter.style.longLine false",
                "",
                f"namespace PrimeCert.LeafGap.{name}",
                "",
                "open PrimeCert",
                "",
            ]
            for r in range(REPEATS):
                rel = [i + 1 for i in survivor_positions(lo, length, small)]
                gaps = [rel[0]] + [rel[i] - rel[i - 1] for i in range(1, len(rel))]
                assert all(0 < g <= MASK for g in gaps), f"{name} has a gap outside the field"
                G = 0
                for i, g in enumerate(gaps):
                    G |= g << (FIELD * i)
                window = 0
                for x in rel:
                    window |= 1 << x
                total = window + P * (rel[-1] + Q * sum(rel))
                lines += [
                    f"/-- {len(rel)} survivors of {length} positions from {lo}. -/",
                    f"public theorem leaf_{r} : "
                    f"Nat.beq (gapFoldPosK {P} {Q} {PQ} {FIELD} {MASK} {G} {len(gaps)}) "
                    f"{total} = true := by",
                    "  quickRfl",
                    "",
                ]
                lo += length
            lines += [f"end PrimeCert.LeafGap.{name}", ""]
            with open(f"{out}/{name}.lean", "w") as f:
                f.write("\n".join(lines))
    print(f"{out}: {len(B_VALUES) * len(LENGTHS)} files of {REPEATS} leaves, "
          f"positions {start} to {lo}")


main()
