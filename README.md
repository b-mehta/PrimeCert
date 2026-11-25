# PrimeCert

This repository provides the canonical way to generate proofs of primality in Lean 4, using Mathlib.
It relies only on Lean's kernel, without trusting the compiler (that is, no use of `native_decide`).
It implements [Pocklington's primality test](https://en.wikipedia.org/wiki/Pocklington_primality_test) and an improved cube-root variant, with custom metaprogramming to make certificates compact and kernel-checkable.

This project is actively maintained by [b-mehta](https://github.com/b-mehta), and has had many vital contributions by [kckennylau](https://github.com/kckennylau).

## Usage

Proofs of primality using this library look like this:
```lean
import PrimeCert

-- Cube-root Pocklington with a supplied nonsquare interval:
example : Nat.Prime 73471 := prime_cert%
  [small {2; 31}, pock3 (73471, 3, interval 68, 2 * 31)]

-- Small primes via classic Pocklington:
theorem prime_31 : Nat.Prime 31 := pock% [2, 3; (31, 3, 2 * 3)]

-- Large primes via the combined framework:
theorem prime_60digit :
    Nat.Prime 236684654874665389773181956283167565443541280517430278333971 := prime_cert%
  [small {2; 3; 29; 31},
   pock3 (73471, 3, 1, interval, 2 * 31),
   pock3 (32560621, 2, 1, interval, 2 ^ 2 * 3 * 29),
   pock3 (3586530508831189, 2, 1, interval, 2 ^ 2 * 73471),
   pock3 (236684654874665389773181956283167565443541280517430278333971,
     2, 1, interval, 2 * 32560621 * 3586530508831189)]
```

For `pock3`, the nonsquare mode is `0` when `s = 0`, `<` when `r² < 8s`, or
`interval w` when `w² < r² - 8s < (w+1)²`. Writing just `interval` computes `w`
during elaboration and inserts its literal into the proof. The kernel checks the two
inequalities; it does not compute a square root. Both four-field and explicit-sieve-bound
five-field forms accept these modes, including a lone power of two such as
`pock3 (197, 2, <, 2 ^ 2)`. Replace former prime-QNR mode numbers with `interval`;
auxiliary primes used only for those witnesses can be removed from `small`.

The series of numbers form a prime certificate. For convenience, we provide a Python script in `scripts/prime_cert.py` to generate these certificates automatically. 
Building such a prime certificate for N requires a (partial) factorisation of N-1. The script attempts to find these using `sympy`, falling back to GNU's `factor`, falling back to Pollard's rho.
However, if you already have such a factorisation, this can also be provided to the script.

```bash
# Build a certificate for 16290860017 (uses sympy via uv, or GNU factor, or built-in rho):
python3 scripts/prime_cert.py 16290860017

# Supply the factorisation of N-1 (for large primes, use alpertron.com.ar/ECM.HTM):
python3 scripts/prime_cert.py 16290860017 '2^4 * 3 * 339392917'
```

## Constructing a reusable certificate in Lean

Import the optional construction module to use `prime_cert?`:

```lean
import PrimeCert
import PrimeCert.Meta.Construction

example : Nat.Prime (2 ^ 255 - 19) := by
  prime_cert?
```

The tactic searches with a deterministic, finite budget, kernel-checks the resulting
proof, and offers a clickable `Try this:` replacement containing the full
`prime_cert%` ladder. Applying it removes factor and certificate search from later
builds; the kernel still checks the certificate. The literal can be replayed with
`PrimeCert`, `PrimeCert.SieveBase`, and a meta import of
`PrimeCert.Meta.SieveLookup`, without importing construction.

The default `PrimeCert.Construction.Budget` permits 512 bits in the evaluated input, depth 32,
1024 total factor/witness attempts, and 1024 worklist steps per factorization.
Pollard p−1 uses bounds 64, 512, 4096, 32768, 262144, 524288 and bases 2, 3;
rho has two restarts of 32768 steps. Witness search tries 2, 3, 5, 7, 11, 13, 17,
then at most 32 candidates from seed 17. Subset selection considers at most 12
factors and 4096 subsets, estimating child-certificate cost before recursion.
The sieve bound is at most 64, allowing up to 63 checks of potential divisors
`l*F+1` in exchange for a smaller factored part `F`. Subset estimates include
these divisions as well as the factor witnesses and recursive children.
Construction first tries the trial-division factors before spending smooth/rho
work, retaining consumed attempts and random state if it must fall back.
Power-of-two-only factorizations are supported; no auxiliary odd prime is needed.
The first successful cheap certificate is used, favoring construction latency
over comparison with certificates that require further factoring. Suggestions
always include the chosen sieve bound explicitly.
There is no ECM or external factorizer on this route. Stage primes come from the
existing certified sieve; a bound outside its coverage fails explicitly.

The bit limit applies after evaluating the closed goal expression. Exhaustion means that
the bounded policy found no certificate; it also covers composite inputs and subset or depth
limits. Custom sieve bounds above the default cache require a matching `run_sieve` in both
the construction and replay context.

Configure the finite policy with `prime_cert? (config := { maxAttempts := 100 })`.
Exhaustion reports consumed attempts and the advanced seed. A failed search does
not imply compositeness. These bounds are a search policy, not a promise to
handle every prime of the allowed bit size.

## Acknowledgements

We thank Joachim Breitner, Oliver Butterley, Anand Rao Tadipatri, and Siddhartha Gadgil for many helpful discussions which shaped this project.
