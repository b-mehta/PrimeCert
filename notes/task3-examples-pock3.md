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

## Remaining issue (root/mode search, not factoring)
Rebuilding the *largest* primes (e.g. the 71-digit factor in the 25519 chain) is still slow, but
the bottleneck is now the search the script does for the pseudo-primitive `root` (and the
non-residue `mode` witness): thousands of modular exponentiations on ~71-digit numbers. This is
a performance issue, not correctness/factoring. The existing ladders already record a working
`root`/`mode` per prime, so the clean next step is to let the pool supply `root`/`mode` too and
skip the search. Then the four large examples regenerate mechanically and verify in CI.

## Status
`prime_16290860017'` converted + verified. Script gained a whole-ladder factor pool (tested).
The four large examples remain on `pock`/`pock%` pending the `root`/`mode` supply above.

## Status
`prime_16290860017'` converted to `pock3` and verified (build of `PrimeCertTest.PrimeListTest`).
The four large examples remain on `pock`/`pock%`, blocked as above; documented, not guessed.
