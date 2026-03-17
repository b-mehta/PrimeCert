# PrimeCert

Formally verified primality certificates in Lean 4, using Mathlib.

Implements [Pocklington's primality test](https://en.wikipedia.org/wiki/Pocklington_primality_test) and an improved cube-root variant, with custom metaprogramming to make certificates compact and kernel-checkable.

## Usage

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

To construct certificates for new primes, factor `N - 1` using an integer factorisation tool such as the [Alpertron ECM calculator](https://www.alpertron.com.ar/ECM.HTM).
