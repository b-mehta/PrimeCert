# PrimeCert

This repository provides the canonical way to generate proofs of primality in Lean 4, using Mathlib.
It relies only on Lean's kernel, without trusting the compiler (that is, no use of `native_decide`).
It implements [Pocklington's primality test](https://en.wikipedia.org/wiki/Pocklington_primality_test) and an improved cube-root variant, with custom metaprogramming to make certificates compact and kernel-checkable.

This project is actively maintained by [b-mehta](https://github.com/b-mehta), and has had many vital contributions by [kckennylau](https://github.com/kckennylau).

## Usage

Proofs of primality using this library look like this:
```lean
import PrimeCert

-- Small primes via classic Pocklington:
theorem prime_31 : Nat.Prime 31 := pock% [2, 3; (31, 3, 2 * 3)]

-- Large primes via the combined framework:
theorem prime_60digit :
    Nat.Prime 236684654874665389773181956283167565443541280517430278333971 := prime_cert%
  [small {2; 3; 7; 11; 29; 31},
   pock3 (73471, 3, 1, 7, 2 * 31),
   pock3 (32560621, 2, 1, 7, 2 ^ 2 * 3 * 29),
   pock3 (3586530508831189, 2, 1, 11, 2 ^ 2 * 73471),
   pock3 (236684654874665389773181956283167565443541280517430278333971,
     2, 1, 3, 2 * 32560621 * 3586530508831189)]
```

The series of numbers form a prime certificate. For convenience, we provide a Python script in `scripts/prime_cert.py` to generate these certificates automatically. 
Building such a prime certificate for N requires a (partial) factorisation of N-1. The script attempts to find these using `sympy`, falling back to GNU's `factor`, falling back to Pollard's rho.
However, if you already have such a factorisation, this can also be provided to the script.

```bash
# Build a certificate for 16290860017 (uses sympy via uv, or GNU factor, or built-in rho):
python3 scripts/prime_cert.py 16290860017

# Supply the factorisation of N-1 (for large primes, use alpertron.com.ar/ECM.HTM):
python3 scripts/prime_cert.py 16290860017 '2^4 * 3 * 339392917'
```

## Acknowledgements

We thank Joachim Breitner, Oliver Butterley, Anand Rao Tadipatri, and Siddhartha Gadgil for many helpful discussions which shaped this project.
