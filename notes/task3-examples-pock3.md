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

## What actually happened

`prime_16290860017'` converted cleanly: its `N-1` fully factors in seconds, so the script emits
a pure-`pock3` ladder (verified by the build).

The four large examples (100-digit, `2^255-19`, `2^448-2^224-1`, ed25519 order) were harder.
Correcting an earlier mischaracterisation: the script **can** reuse proven factors (the
README's supplied-factorisation feature), but the stock code honoured it only for the *top* `N`
— every sub-prime was re-factored via `factor(p-1)`, which stalls on the large primes in these
chains. A `pock`/`pock3` cert factors only *part* of each `N-1`, so a re-derivation needs those
factorisations threaded through the whole recursion.

## Fix delivered: a factor pool
`scripts/prime_cert.py` now takes `--pool=FILE` (lines `prime: factorisation`) and consults it
at **every** level of the recursion, so a certificate rebuilds from an existing ladder with no
new factoring. Verified: `31757755568855353` (fully pool-covered) certifies instantly with zero
`factor()` calls; the auto-factor path is unchanged.

## The real bottleneck (found by tracing, two wrong guesses corrected)
It was neither factoring (pool solved it) nor the `root`/`mode` search (both fast — root
`a = 2` found in 0.00s) nor the sieve `m`-loop (`m = 1` valid immediately). Tracing `go` showed
it stalled between "factored" and "F selected", in:

```python
F, target = 1 << e, int(p ** (1/3)) + 2
while (target + 1) ** 3 <= p: target += 1
```

`int(p ** (1/3))` is a **float** cube root (~16 sig digits); for a 71-digit `p` it is off from
the true integer cube root by ~1e7, so the `while` walks `target` up one at a time, cubing a
71-digit integer each step — ~1e7 big-integer cubings (tens of seconds to minutes). Small
primes are unaffected (the float is exact enough).

**Fixed** by replacing it with an exact integer cube root `icbrt` (Newton's method, ~5 steps
regardless of size). The 71-digit prime dropped from >90s to 0.04s; the full `2^255-19`
certificate regenerates as pure `pock3` in 0.05s.

## Status
`prime_16290860017'` converted + verified. Script now (a) reuses proven factors at every level
(`--pool`) and (b) uses an exact integer cube root. With both, all four large examples
regenerate instantly (verified for `2^255-19`). Substituting them into `PrimeListTest.lean` and
CI-verifying is the remaining mechanical step.
