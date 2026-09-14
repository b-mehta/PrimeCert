# Harmonic benchmark cases

One bound per file, so one file check times one case. None of these is in `defaultTargets`.

| file | what it measures |
| --- | --- |
| `Base0_Startup.lean` | startup, imports, and the `run_sieve 1000000` in `PrimeCert.SieveBase`; no kernel work of its own |
| `Base1_Sieve1e7.lean` | `Base0` plus `run_sieve 10000000` |
| `Base2_Sieve1e8.lean` | `Base0` plus `run_sieve 100000000` |
| `N1e4.lean` | `Base0` plus the two folds over 3332 positions (1 batch) |
| `N1e5.lean` | `Base0` plus the two folds over 33332 positions (2 batches) |
| `N1e6.lean` | `Base0` plus the two folds over 333332 positions (17 batches) |
| `N1e7.lean` | `Base1` plus the two folds over 3333332 positions (163 batches) |
| `N1e8.lean` | `Base2` plus the two folds over 33333332 positions (1628 batches) |

Every case runs `run_harmonic <bound> 20 20480`: scale `10 ^ 20`, batch length 20480 wheel
positions. The batch length is the same across all five cases on purpose, so the per-batch kernel
reduction is the constant and the batch count is the variable.

## Why 20480

The proof of each fold equation nests one `sumB_chain` application per batch, and a long enough
chain is rejected by the kernel with "deep recursion detected". The segmented-sieve work bisected
that ceiling for *its* chain lemma and bracketed it between 2605 and 5209 links: 2605, 1303 and
652 were accepted, 5209 and 20834 rejected.

20480 is the smallest batch length that puts every case here under 2000 links, the band those
accepted cases occupy. `N1e8` is the binding case at 1628. 16384 would leave it at 2035, over the
band.

Two caveats on that number:

- The ceiling is a bracket, not a measured boundary, and it was measured against a different
  chain lemma (`segLoopK_chain`, not `sumB_chain`). It may not transfer exactly.
- Raising the batch length shortens the chain and enlarges each individual kernel reduction.
  Nobody has measured what the second half of that trade costs. At `N1e8` the two constraints are
  close: the smallest batch the depth band allows is already larger than a single reduction that
  has been reported to exhaust memory elsewhere. If `N1e8` fails, read its failure mode before
  changing the batch length, because the two constraints push in opposite directions.

Both the scale and the batch length are command parameters, so a sweep of either needs no code
change.

Each case's expected `A` and `C`, computed independently of Lean by a wheel sieve in Python:

| bound | positions | `A` at scale `10 ^ 20` | `C` |
| --- | --- | --- | --- |
| `10 ^ 4` | 3332 | 164972661390022729669 | 1227 |
| `10 ^ 5` | 33332 | 187193884571393076680 | 9590 |
| `10 ^ 6` | 333332 | 205399476623433898743 | 78496 |
| `10 ^ 7` | 3333332 | 220811604794637384811 | 664577 |
| `10 ^ 8` | 33333332 | 234164189658716328899 | 5761453 |

`C` is `π(bound) - 2`, the two missing primes being 2 and 3, which the mod-6 wheel does not carry
and `primeRecipIcc_of` adds back as `5 / 6`. The command recomputes both literals itself, so
these are a cross-check rather than an input.

Only `Base0_Startup`, `N1e4` and `N1e5` have ever been run. `N1e6`, `N1e7`, `N1e8`,
`Base1_Sieve1e7` and `Base2_Sieve1e8` are unrun and unchecked.
