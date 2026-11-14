"""Emit the Lean lines for a design-sized chunk test.

The checks in ChunkProductProbe use four-record chunks, which say the definition is right and
nothing about whether it reduces at the size the design actually calls for. The sizing settled on
256 records a chunk, depth 8. This prints the two literals that test needs so they are generated
rather than typed: the packed record set, and the product it should reduce to.

Positions 0 to 255, so the records are i at slot i, and the product is the first 256 values
coprime to 6.
"""

# 64 rather than the design's 256. At 256 the packed records are a 1230-digit literal, too large
# to carry in a source file sensibly, and a script may not write the Lean itself. 64 records at
# depth 6 is still a long way past the four-record checks and exercises the same recursion.
N = 64
REC_BITS = 16


def valK(k: int) -> int:
    return 3 * k + 1 + k % 2


recs = 0
for i in range(N):
    recs |= i << (REC_BITS * i)

prod = 1
for i in range(N):
    prod *= valK(i)

asm = 0
for i in range(N):
    asm |= 1 << i

DEPTH = 8  # the design's chunk depth; with N below it also exercises the cutoff at scale

print(f"-- {N} records at positions 0 to {N - 1}, in {2 ** DEPTH} slots at depth {DEPTH}, so the")
print(f"-- {2 ** DEPTH - N} slots past the count contribute the identity.")
print(f"-- recs is {recs.bit_length()} bits, the product {prod.bit_length()}.")
print()
print(f"private def recsChunk : Nat := {recs}")
print()
print(f"example : prodChunkK recsChunk 0 {N} {DEPTH} 0 = {prod} := rfl")
print(f"example : asmChunkK recsChunk {N} {DEPTH} 0 = {asm} := rfl")
