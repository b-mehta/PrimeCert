"""Emit kernel checks that price one running-sum update of the paper's identity.

Sweeping a segment, the identity carries one running sum for each of the `a` primes below the
cut, and clearing a multiple updates the sums above it. With no mutable store the sums live side
by side in one literal, so an update is an addition into a field of a wide number and its cost is
set by that number's width, not by the size of what is added.

Each theorem folds `steps` updates into a literal holding `fields` sums of `bits` each, cycling
through the fields, and the kernel settles it against the value computed here.

Usage: gen_update_probe.py OUT_DIR START_VALUE STEPS [FIELDS] [BITS] [REPEATS]
"""

import sys

sys.set_int_max_str_digits(1000000)


def main() -> None:
    out = sys.argv[1]
    seed = int(sys.argv[2])
    steps = int(sys.argv[3])
    fields = int(sys.argv[4]) if len(sys.argv) > 4 else 4797
    bits = int(sys.argv[5]) if len(sys.argv) > 5 else 60
    repeats = int(sys.argv[6]) if len(sys.argv) > 6 else 2

    name = f"U{fields}_{steps}"
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
        f"/-! # {repeats} folds of {steps} running-sum updates",
        "",
        f"The identity carries one running sum for each of the {fields} primes below its cut, and",
        "sweeping a segment updates them as multiples are cleared. With no mutable store the sums",
        f"sit side by side in one literal of {fields * bits} bits, so an update adds into a field",
        "of a wide number and costs what that width costs, not what the addend costs.",
        "",
        "Nothing here is proved to be an update of anything; the file is for timing.",
        "-/",
        "",
        "set_option linter.style.longLine false",
        "set_option maxRecDepth 4000000",
        "",
        f"namespace PrimeCert.UpdateProbe.{name}",
        "",
        "open PrimeCert",
        "",
        "/-- One sweep of updates over the packed sums, in the operations the kernel reads. -/",
        "@[expose] public noncomputable def updateFold (W0 F M c : ℕ) : ℕ :=",
        "  c.rec W0 fun i st ↦",
        "    Nat.add st (Nat.shiftLeft (nat_lit 1) (Nat.mul F (Nat.mod i M)))",
        "",
    ]

    for r in range(repeats):
        start = seed + r
        base = sum((start + k) % 7 + 1 << (bits * k) for k in range(fields))
        total = base + sum(1 << (bits * (i % fields)) for i in range(steps))
        lines += [
            f"/-- {steps} updates into {fields} fields of {bits} bits. -/",
            f"public theorem sweep_{r} : "
            f"Nat.beq (updateFold {base} {bits} {fields} {steps}) {total} = true := by",
            "  quickRfl",
            "",
        ]
    lines += [f"end PrimeCert.UpdateProbe.{name}", ""]

    with open(f"{out}/{name}.lean", "w") as f:
        f.write("\n".join(lines))
    print(f"{out}/{name}.lean: {repeats} folds of {steps} updates, "
          f"{fields} fields of {bits} bits, literal {fields * bits} bits")


main()
