/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import PrimeCert.PowMod

/-! Kernel regression tests for fixed-window modular exponentiation. -/

example : powModK 0 0 0 = 1 := by decide +kernel
example : powModK 0 17 0 = 0 := by decide +kernel
example : powModK 7 17 0 = 7 ^ 17 := by decide +kernel
example : powModK 7 0 1 = 0 := by decide +kernel
example : powModK 5 3 1 = 0 := by decide +kernel
example : powModK 2
    57896044618658097711785492504343953926634992332820282019728792003956564819948
    57896044618658097711785492504343953926634992332820282019728792003956564819949 = 1 := by
  decide +kernel

-- Full bases exercise each modulus threshold, including the binary fallback.
example : [64, 512, 1024, 2048, 4096].all (fun bits =>
    [2 ^ bits - 1, 2 ^ bits, 2 ^ bits + 1].all (fun m =>
      powModK (m - 3) 17 m == m - 129140163)) := by decide +kernel

-- These inputs cross the small-base cutoff and its two-/one-bit window transition.
example : [2048, 4096].all (fun bits =>
    [2 ^ 64 - 1, 2 ^ 64].all (fun a =>
      powModK a 17 (2 ^ bits + 1) == a ^ 17 % (2 ^ bits + 1))) := by decide +kernel

example : [1, 2, 3, 7, 8, 9, 15, 16, 17, 63, 64, 65].all (fun e =>
    powModK 7 e 97 == 7 ^ e % 97) := by decide +kernel

example : let m := 2 ^ 4096 + 1
    powModK 2 (2 ^ 64) m = 1 := by decide +kernel

-- A full base and a multi-level exponent in the six-bit window.
example : powModK (2^64-5) (2^64-3) (2^64-59) = 13725768017768333112 := by
  decide +kernel
