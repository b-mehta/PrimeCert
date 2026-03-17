/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import PrimeCert.Meta.PrimeCert

/-! # The `small` certificate method

Looks up a pre-existing `PrimeCert.prime_N` declaration (from `SmallPrimes.lean`).
Used as a base case in certificate ladders for primes below ~1000.
-/

open Lean Meta Elab Qq

namespace PrimeCert.Meta

/-- Syntax for the `small` method: just a numeric literal `n`.
Looks up the declaration `PrimeCert.prime_n` in the environment.

```lean
-- In a prime_cert% call:
prime_cert% [small {2; 3; 5; 7}, ...]
-- Each number must have a corresponding `PrimeCert.prime_N` theorem.
```
-/
syntax small_spec := num

def mkSmallProof : PrimeCertMethod ``small_spec := fun stx _ ↦ match stx with
  | `(small_spec| $n:num) => do
    have n := n.getNat
    have name : Name := (`PrimeCert).str s!"prime_{n}"
    return ⟨n, mkNatLit n, mkConst name⟩
  | _ => throwUnsupportedSyntax

@[prime_cert small] def PrimeCertExt.small : PrimeCertExt where
  syntaxName := ``small_spec
  methodName := ``mkSmallProof

end PrimeCert.Meta
