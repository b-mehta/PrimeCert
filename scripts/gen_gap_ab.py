"""Emit a two-arm probe comparing the gap walk that divides against one that sums positions.

Both arms walk the same packed gaps over the same batches, so the only difference is what each
step adds to the total: `gapFoldK` adds `S / value (lo + position)`, `gapFoldPosK` adds the
position. Nothing here is proved; the file exists to be timed, with the kernel settling each
`Nat.beq` against a literal computed below.

Usage: gen_gap_ab.py OUT START_POSITION BATCHES [BATCH_LEN]
"""

import sys

FIELD = 8          # bits per packed gap
MASK = (1 << FIELD) - 1
Q = 1 << 32        # position field width
SCALE = 10 ** 20


def value(k: int) -> int:
    """The k-th integer coprime to 6, counting value(0) = 1."""
    return 3 * k + 1 + (k % 2)


def sieve_upto(n: int) -> list[int]:
    flags = bytearray([1]) * (n + 1)
    flags[0:2] = b"\x00\x00"
    p = 2
    while p * p <= n:
        if flags[p]:
            flags[p * p :: p] = bytearray(len(flags[p * p :: p]))
        p += 1
    return [i for i in range(n + 1) if flags[i]]


def primes_in(lo: int, hi: int) -> set[int]:
    """Primes in [lo, hi), by sieving the interval with the primes up to sqrt(hi)."""
    base = sieve_upto(int(hi ** 0.5) + 1)
    flags = bytearray([1]) * (hi - lo)
    for p in base:
        start = max(p * p, ((lo + p - 1) // p) * p)
        for m in range(start, hi, p):
            flags[m - lo] = 0
    return {lo + i for i, f in enumerate(flags) if f}


def main() -> None:
    out, start, batches = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    blen = int(sys.argv[4]) if len(sys.argv) > 4 else 2048

    P = 1 << (blen + 1)
    PQ = P * Q

    first, last = value(start), value(start + batches * blen) + 1
    prime = primes_in(first, last)

    arms = []
    for b in range(batches):
        p0 = start + b * blen
        lo = p0 - 1
        hits = [k for k in range(p0, p0 + blen) if value(k) in prime]
        rel = [k - lo for k in hits]
        gaps = [rel[0]] + [rel[i] - rel[i - 1] for i in range(1, len(rel))]
        assert all(0 < g <= MASK for g in gaps), f"batch {b} has a gap outside the field"

        G = 0
        for i, g in enumerate(gaps):
            G |= g << (FIELD * i)
        window = 0
        for r in rel:
            window |= 1 << r
        pos = rel[-1]
        total_div = sum(SCALE // value(lo + r) for r in rel)
        total_pos = sum(rel)
        arms.append((b, lo, len(gaps), G,
                     window + P * (pos + Q * total_div),
                     window + P * (pos + Q * total_pos)))

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
        "/-! # The gap walk that divides, against the gap walk that sums positions",
        "",
        f"{batches} batches of {blen} wheel positions from position {start}, whose numbers begin at",
        f"{value(start)}. Each batch appears twice over the same packed gaps: `div_i` adds",
        "`10 ^ 20` divided by the number at each position reached, `pos_i` adds the position. The",
        "offset expansion encloses the sum of reciprocals from the count and the sum of positions,",
        "so the second arm reaches the same enclosure with an addition where the first divides.",
        "",
        "Nothing here is proved to agree with `sumB (recipAtW ...)`; the file is for timing.",
        "-/",
        "",
        "set_option linter.style.longLine false",
        "",
        "namespace PrimeCert.GapAB",
        "",
        "open PrimeCert",
        "",
    ]
    for b, lo, c, G, exp_div, exp_pos in arms:
        for tag, fold, exp in (
            ("div", f"gapFoldK {P} {Q} {PQ} {FIELD} {MASK} {G} {lo} {SCALE} {c}", exp_div),
            ("pos", f"gapFoldPosK {P} {Q} {PQ} {FIELD} {MASK} {G} {c}", exp_pos),
        ):
            lines += [
                f"public theorem {tag}_{b} : Nat.beq ({fold}) {exp} = true := by quickRfl",
                "",
            ]
    lines += ["end PrimeCert.GapAB", ""]

    with open(out, "w") as f:
        f.write("\n".join(lines))
    print(f"{out}: {batches} batches, {sum(a[2] for a in arms)} gaps in each arm")


main()
