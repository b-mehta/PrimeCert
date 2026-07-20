# Task 1: a `prime_cert` tactic (superseding the `prime_cert%` term elaborator)

## Goal
Turn the `prime_cert%` term elaborator into a tactic `prime_cert` that closes primality
goals, and additionally handle conjunctions such as `Nat.Prime p ∧ Nat.Prime q` and the
general `Prime p` (mathlib's `_root_.Prime`), not just a bare `Nat.Prime p`.

Back-compat (task 5): `prime_cert%` is **not** deleted. It stays and is marked deprecated,
emitting a warning that points at the tactic.

## Current design (master)
`Meta/PrimeCert.lean` defines:
- `PrimeDict := Std.HashMap Nat Expr` — maps a certified `n` to a proof term of `Nat.Prime n`.
- `primeCertExt` — a scoped env extension holding the registered methods (`small`, `pock`,
  `pock3`), keyed by string.
- `prime_cert% [g₁, …, gₙ]` — a `term` elaborator. It walks the groups, runs each method,
  inserts every certified prime into `dict`, and returns the proof of the **last** one.

The ladder-running loop and the goal selection are entangled inside the one elaborator.

## Plan
1. **Factor** the ladder loop into a reusable
   `runPrimeCertLadder : Array (TSyntax \`step_group) → TermElabM PrimeDict`
   that returns the full dict (every certified prime, with its proof term), instead of only
   the last one. Both the term elaborator and the tactic call it.
2. **Term elaborator** `prime_cert%` becomes a thin wrapper: run the ladder, return the proof
   of the last certified prime (unchanged behaviour), plus a deprecation warning.
3. **Tactic** `prime_cert [g₁, …, gₙ]`: run the ladder to build `dict`, then close the main
   goal with a recursive `closePrimeGoal`:
   - `A ∧ B`  → `apply And.intro`, recurse on both subgoals.
   - `Nat.Prime n` (n a literal) → look up `n` in `dict`, `assign`.
   - `Prime (n : ℕ)` → look up `n`, wrap with `Nat.Prime.prime`.
   - anything else → informative error.

## Why a shared `runPrimeCertLadder`
The tactic and the term form must agree on how the ladder is walked; sharing one function
avoids drift and keeps the deprecation of `prime_cert%` a one-liner.

## Open questions / decisions
- The goal's certified primes must all appear as steps in the ladder (the tactic does not
  discover a factorisation; it only assembles proofs the ladder produced). This matches how
  `prime_cert%` already works, so it is not a regression.
- `Prime` bridging uses `Nat.Prime.prime : p.Prime → Prime p` (verify the exact name).
- Deprecating an `elab`: emit `logWarning`/`Linter.logLintIf`-style deprecation from inside
  the elaborator (there is no `@[deprecated]` that attaches cleanly to bespoke `elab` syntax).

## Status
Implemented in `Meta/PrimeCert.lean`; `prime_cert%` retained + deprecated. Tests added under
`PrimeCertTest`. See the commit on branch `task1-prime-cert-tactic`.
