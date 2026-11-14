"""What chunk size should the record certificate use, and how big is each statement?

The certificate has to be many small statements rather than a few large ones, because a definition
reaching record `j` by shifting the packed set walks it every time: the operand size per statement
is what matters, not the operation. 256 records was a guess by analogy with what a batch puts in a
slot. This works out the actual numbers so the next implementation does not have to guess.

Counts and byte sizes only. Nothing here says what a statement costs to check.

Sizes: a record is 16 bits. A window value near 1e14 is about 47 bits, a divisor up to 1e7 about
23. A chunk's product is the sum of its factors' bits, since multiplying adds lengths.
"""

LIVE = 390802        # live values of the finished window, which are its primes
SKIP = 435226        # divisors the sweep skips
VAL_BITS = 47        # log2 of a window value near 1e14
DIV_BITS = 23        # log2 of a divisor up to 1e7
REC_BITS = 16

P_BYTES = SKIP * DIV_BITS / 8    # the product of every skipped divisor, referenced by each gcd

print(f"P, the product of all {SKIP} skipped divisors: {P_BYTES / 1e6:.2f} MB")
print()
print("P must be emitted as its own definition and referenced by name. Inlined as a literal into")
print("every live-side statement it would be repeated thousands of times, and the file would carry")
print(f"that {P_BYTES / 1e6:.2f} MB once per statement instead of once.")
print()

print(f"{'chunk':>7} {'live stmts':>11} {'recs/stmt B':>12} {'prod/stmt B':>12} "
      f"{'skip stmts':>11} {'skip prod B':>12}")
for c in (64, 128, 256, 512, 1024, 4096, 16384):
    live_stmts = -(-LIVE // c)
    skip_stmts = -(-SKIP // c)
    recs_b = c * REC_BITS / 8
    prod_b = c * VAL_BITS / 8
    skip_prod_b = c * DIV_BITS / 8
    print(f"{c:7} {live_stmts:11} {recs_b:12.0f} {prod_b:12.0f} {skip_stmts:11} {skip_prod_b:12.0f}")

print()
print("The trade: a smaller chunk shrinks the record set each statement shifts through, and the")
print("partial product it builds, but states more of them. The route's own slots sit at a few")
print("hundred records, which is the only point on this table with evidence behind it.")
print()
tot = (LIVE * REC_BITS + LIVE * VAL_BITS + SKIP * REC_BITS + SKIP * DIV_BITS) / 8
print(f"Total record and product bytes across all statements, chunk-independent: {tot / 1e6:.2f} MB")
print(f"against the window's own {4194304 / 8 / 1e6:.2f} MB.")
