# Task 6: pow-mod — pure reflection vs. partial-in-elaborator, and a hybrid

## Aim
Re-benchmark the two ways to build a kernel proof of `powMod a b n = m`, on **large** inputs,
**in CI** (noiseless, fair), heavily optimised. Investigate a hybrid. The concrete target is to
make the currently-commented ~700-digit example work again
(`PrimeCertTest/PrimeListTest.lean`, `3 * 2^3912 + 1`, exponent ≈ 3912 bits).

## The two approaches (from `b-mehta/mathlib4@large-prime:Mathlib/V2/PowMod.lean`)

**B — pure reflection** (what PrimeCert ships today, `PowMod.lean`):
- `powModTR'` computes `a^b % n` in the elaborator; the emitted proof is a single
  `powMod_eq_of_powModTR a b n m (eagerReduce (Eq.refl true))`.
- Correctness is discharged by the **kernel** reducing `powModTR a b n |>.beq m` to `true`.
- Cost is one giant kernel reduction: `Nat.rec` over `b.succ` fuel, doing `Nat` `mul`/`mod`
  on numbers up to `n`. For a 3912-bit exponent this is ~3912 iterations of big-`Nat`
  arithmetic *inside the kernel*, which is why the example needs `maxRecDepth 7844` and a huge
  `exponentiation.threshold`, and is slow/fragile.

**A — partial in the elaborator** (`prove_pow_mod`, not currently in PrimeCert):
- `mkPowModAuxEq` recurses on the exponent *in `MetaM`*: at each bit it computes `a*a % n` and
  `a*c % n` in the elaborator and emits `powModAux_{even,odd}_eq` glued by `mkEqRefl` (a small
  `rfl` that the kernel checks cheaply).
- The kernel checks ≈ (bits of `b`) small `rfl`s instead of one enormous reduction. The
  elaborator does the arithmetic (fast, compiled `Nat`), the kernel only *verifies* each step.
- Proof term is larger (a chain), but each kernel check is tiny — likely far better behaved for
  huge exponents (no deep `Nat.rec` fuel, no `maxRecDepth` blow-up).

The reference file exposes both as `prove_pow_mod` (A) and `prove_pow_mod2` (B), which is
exactly the harness needed to compare them.

## Why this matters for the 700-digit example
The example is commented with `-- TODO: fix this example`. It is a single `pock%` step with a
`2 ^ 1957`-sized `F` and a ~3912-bit exponent. Under pure reflection (B) the kernel must reduce
`powModTR` with ~3912 units of fuel over ~1178-digit `Nat`s — the source of the `maxRecDepth`
/ `exponentiation.threshold` gymnastics and the reason it was disabled. Approach A (or a
hybrid) should make it tractable because the per-step kernel work is bounded.

## Benchmark methodology (must be CI, not this shared box)
The shared dev box is noisy; a fair comparison needs a dedicated CI runner.
- **Harness**: a file that proves `powMod 2 (2^k - 1) p = …` (and `≠`) for increasing `k`
  (e.g. 2^6, 2^8, 2^10, 2^12, 2^13 bits), once with `prove_pow_mod` (A) and once with
  `prove_pow_mod2` (B), each under `set_option trace.profiler true` / `#time`.
- **Measure separately**: (i) elaboration time (elaborator arithmetic + proof-term
  construction) and (ii) kernel checking time (`count_heartbeats` / profiler `kernel` bucket).
  A only shifts work between these; the interesting number is total wall-clock and peak
  `maxRecDepth`.
- **Noiselessness**: pin the CI runner, disable `native_decide`, run each point a few times,
  report medians. Emit machine-readable timings (JSON) so runs are comparable across commits.
- **Big**: push `k` until one approach fails (`maxRecDepth`, timeout) — that boundary is the
  headline result.

## Hybrid ideas to investigate
1. **Threshold switch**: use B (pure reflection) below some exponent-bit threshold (small proof
   term, one fast reduction) and A above it (bounded kernel steps). Pick the threshold from the
   benchmark crossover.
2. **Chunked reflection**: reflect the exponent in windows of `w` bits — each window is one
   `eagerReduce` over `w` fuel, glued by `powModAux_*`-style step lemmas. `w = 1` is pure A,
   `w = ∞` is pure B; tune `w` to minimise total time.
3. **Windowed exponentiation** (`2^w`-ary): precompute `a^0..a^(2^w-1) % n` in the elaborator,
   emit fewer, larger steps. Standard fast-exp optimisation, orthogonal to A/B.

## Delivered here
- **Approach A ported into the repo.** `PrimeCertTest/PowModBench.lean` adds the
  `powModAux_{zero,one,even,odd}_eq` step lemmas, `mkPowModAuxEq`, and the tactic
  `prove_pow_mod_steps`, alongside PrimeCert's existing approach B (`prove_pow_mod`).
- **Benchmark harness.** The same fact is proved by both tactics at 256/1024/2048-bit exponents
  under `#time`; results `r = 2^e mod n` are exact by construction. Both tactics verify (the
  file builds).

Local `#time` (shared box, noisy; elaboration only — **not** the fair comparison):
`256b` B 12ms / A 15ms; `1024b` B 14ms / A 114ms; `2048b` B 13ms / A 400ms. Caveat: `#time`
captures elaboration, and B's cost is mostly in *kernel checking* of the `eagerReduce` term,
which `#time` does not attribute — so no conclusion is drawn here.

## Next steps (need a pinned CI runner)
1. **Measure fairly on CI**: run the harness with `count_heartbeats` / the profiler's kernel
   bucket so elaboration vs. kernel time are separated; medians over a few runs; push the size
   gradient up to the ~3912-bit exponent of the 700-digit example.
2. From the crossover, **implement the hybrid** (threshold switch, or chunked/windowed
   reflection — see options above).
3. **Re-enable the 700-digit example** as the acceptance test once the hybrid lands.

Reference (both tactics side by side): `b-mehta/mathlib4@large-prime:Mathlib/V2/PowMod.lean`.
