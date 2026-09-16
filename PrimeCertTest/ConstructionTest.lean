/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
import PrimeCert
import PrimeCert.Meta.Construction
meta import PrimeCert.Construction

/-! Bounded construction, deterministic literal suggestions, and failure diagnostics. -/

/--
info: Try this:
  [apply] exact prime_cert%
    [sieve {101}]
-/
#guard_msgs in
example : Nat.Prime 101 := by prime_cert?

/--
info: Try this:
  [apply] exact prime_cert%
    [sieve {2; 5; 4153; 57467; 132049; 430751},
     pock (31757755568855353, 2, 4153 * 430751),
     pock3 (74058212732561358302231226437062788676166966415465897661863160754340907, 2, 5, 2 * 57467 * 132049 * 31757755568855353),
     pock (57896044618658097711785492504343953926634992332820282019728792003956564819949, 2, 74058212732561358302231226437062788676166966415465897661863160754340907)]
-/
#guard_msgs in
example : Nat.Prime (2 ^ 255 - 19) := by prime_cert?

/--
error: prime_cert?: construction exhausted after 1 attempts (limit 1, depth 32, seed 17)
-/
#guard_msgs in
example : Nat.Prime (2 ^ 255 - 19) := by
  prime_cert? (config := { maxAttempts := 1 })

/-- error: prime_cert?: construction input exceeds 32 bits -/
#guard_msgs in
example : Nat.Prime (2 ^ 255 - 19) := by prime_cert? (config := { maxBits := 32 })

-- A pure power of two cannot yet be rendered by the existing pock3 syntax.
/--
error: prime_cert?: construction exhausted after 0 attempts (limit 1024, depth 32, seed 17)
-/
#guard_msgs in
example : Nat.Prime 37 := by
  prime_cert? (config := { trialBound := 2, smoothBounds := [], factorFuel := 0 })

open PrimeCert.Construction

-- These are executable producer checks, separate from the kernel replay tests.
set_option linter.hashCommand false

#guard !validate 101 ⟨[(2, 2), (2, 1)], 1⟩ 12
#guard !validate 101 ⟨[(2, 1000000000)], 1⟩ 12
#guard !validate 101 ⟨[(1, 1)], 100⟩ 12
#guard !validate 101 ⟨[(2, 2)], 24⟩ 12
#guard !validate 101 ⟨[(2, 2)], 0⟩ 12
#guard validate 101 ⟨[(2, 2), (5, 2)], 1⟩ 12

run_cmd Lean.Elab.Command.liftTermElabM do
  let primes ← PrimeCert.Meta.constructionPrimes 524288
  unless primes.size == 43390 && primes.back? == some 524287 do
    throwError "incorrect sieve endpoint"
  for bound in [0, 1, 2, 3, 4, 5, 524287, 524288, 524289] do
    let actual ← PrimeCert.Meta.constructionPrimes bound
    unless actual == primes.filter (· ≤ bound) do throwError "endpoint mismatch at {bound}"
  let hard :=
    (74058212732561358302231226437062788676166966415465897661863160754340907 - 1) /
      (2 * 3 * 353 * 57467 * 253947789517)
  unless pMinusOne primes hard 2 262144 == .noFactor do throwError "lower boundary"
  unless pMinusOne primes hard 2 524288 == .factor 31757755568855353 do
    throwError "upper boundary"
  unless pMinusOne primes 15 4 2 == .whole do throwError "whole modulus"
  let a := run {} primes (2^255-19)
  let b := run {} primes (2^255-19)
  unless a == b && a.1 && a.2.attempts ≤ 1024 do throwError "non-deterministic search"
  unless !(run { maxDepth := 0 } primes (2^255-19)).1 do throwError "depth exhaustion"
  unless !(run { maxAttempts := 0 } primes (2^255-19)).1 do throwError "attempt exhaustion"
  unless !(run {} primes (2^255-17)).1 do throwError "composite accepted by construction"

/--
info: Try this:
  [apply] exact prime_cert%
    [sieve {101}]
-/
#guard_msgs in
example : Nat.Prime 101 := by prime_cert? (config := { maxAttempts := 2 ^ 10 })

/-- error: prime_cert?: expected a closed natural number -/
#guard_msgs in
example (n : Nat) : Nat.Prime n := by prime_cert?

/-- error: prime_cert?: expected a goal of the form `Nat.Prime _` -/
#guard_msgs in
example : True := by prime_cert?
