# Task 3: make the examples use `pock3`, not `pock`

## Goal
The showcase/test examples should demonstrate `pock3` (cube-root Pocklington) rather than the
older `pock` (full Pocklington). Back-compat: `pock`/`pock%` themselves are not removed (they
remain valid methods); only *our examples* stop using them.

## Where `pock` appears (in the examples, `PrimeCertTest/PrimeListTest.lean`)
1. `prime_16290860017'` — `pock% [...]` (line 22).
2. a randomly generated 100-digit prime — `pock% [...]` (line 37).
3. `prime_25519` (`2^255 - 19`) — a `prime_cert%` ladder that is all `pock3` **except** the
   final top-prime step, which is `pock` (line 58).
4. `prime_448_224_1` (`2^448 - 2^224 - 1`) — same shape: one `pock` step (line 68).
5. `prime_ed25519_order` (`2^252 + …`) — `pock% [...]` (line 93).

(The `pock%`/`pock` occurrences inside `Meta/Pocklington.lean` are that method's own
documentation and are intentionally left — they document a feature that still exists.)

## Method
The repo already ships `scripts/prime_cert.py`, which **emits pure-`pock3`** `prime_cert%`
certificates (it never uses `pock`). So each conversion is: regenerate the certificate for `N`
with the script, then replace the `pock`/`pock%` version.

- Small / chained primes (16290860017, the 100-digit, the ed25519 order): the script
  auto-factors `N-1` (sympy via `uv`). The chained examples have `N-1 = (previous prime) ·
  (small cofactor)`, which factors easily.
- `2^255-19` and `2^448-2^224-1`: `N-1` is hard to auto-factor, but the existing ladders
  already list every needed prime factor. Supply the `N-1` factorisation to the script
  (`python3 scripts/prime_cert.py N 'factorisation'`) to regenerate as pure `pock3`.

## Notes
- The generated theorems are named `prime_<N>`; existing example names (`prime_16290860017'`,
  `prime_25519`, `prime_448_224_1`) are preserved by keeping the `theorem <name> : … := ` line
  and substituting only the `prime_cert% [...]` body.
- Each conversion is verified by building `PrimeCertTest.PrimeListTest` (the certificates are
  kernel-checked, so a successful build *is* the proof they are correct).
- `maxRecDepth` / `exponentiation.threshold` `set_option`s are kept as needed per example.

## What actually happened (blocker found)

Only `prime_16290860017'` converted cleanly: its `N-1` fully factors in seconds, so the script
emits a pure-`pock3` ladder, and it is verified by the build.

The four large examples (100-digit, `2^255-19`, `2^448-2^224-1`, ed25519 order) are **blocked**:

- A `pock`/`pock3` certificate deliberately factors only *part* of `N-1` (`F`, with the
  cofactor `R = (N-1)/F` left unfactored — that is the whole point of Pocklington). So the
  existing certificates do **not** contain a full factorisation of `N-1`.
- Regenerating a certificate with the script therefore requires re-factoring `N-1` from
  scratch. sympy (via `uv`) timed out (>300–400s) on each of these — factoring a 100+-digit
  `N-1` with a large prime factor is the genuinely hard step (the README itself points to
  alpertron ECM for this).
- The script cannot reuse the factorisations already present in the existing ladder; it
  re-factors each level independently and hits the same wall on the large primes.

So auto-conversion of the large examples is not feasible without either (a) supplying the full
`N-1` factorisations (obtained out-of-band via ECM / alpertron), or (b) teaching the script /
a new tool to reuse the factorisations the existing ladder already proves. Both are real work
and a design decision, so they are left for review rather than guessed at overnight.

## Recommendation
Extend `scripts/prime_cert.py` (or a companion) to accept the existing ladder and reuse its
proven prime factors, so a `pock`→`pock3` re-derivation needs no new factoring. Then the four
large examples convert mechanically. Flagged for Bhavik.

## Status
`prime_16290860017'` converted to `pock3` and verified (build of `PrimeCertTest.PrimeListTest`).
The four large examples remain on `pock`/`pock%`, blocked as above; documented, not guessed.
