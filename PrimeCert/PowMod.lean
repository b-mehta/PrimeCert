/-
Copyright (c) 2022 Bhavik Mehta and 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum.PowMod
public import PrimeCert.ForLean

/-!
# Proof-producing evaluation of `a ^ b % n`

Note that `Mathlib.Tactic.NormNum.PowMod` contains a similar tactic, but that runs significantly
slower and less efficiently than the one here.

The accumulator was developed by Bhavik Mehta with help from Joachim Breitner.
The fixed-window implementation follows leanprover/lean4#15167.
-/

open Nat

/-- The pow-mod auxiliary function, named explicitly to allow more precise control of reduction. -/
def powModAux (a b c n : ℕ) : ℕ := (a ^ b * c) % n

/-- Fixed-window loop: `window b m k fuel e` computes `b ^ e % m` when
`2 ≤ k` and `e < fuel`. The small powers use the kernel's `Nat.pow` reduction. -/
@[expose] public noncomputable def powModK.window (b m k : Nat) : Nat → Nat → Nat :=
  Nat.rec (fun _ => 0)
    (fun _ rec e =>
      (e.beq 0).rec
        ((((rec (e.div k)).pow k).mul (b.pow (e.mod k))).mod m)
        ((1 : Nat).mod m))

private theorem powModK.window_eq (b m k fuel e : Nat) (hk : 2 ≤ k) (h : e < fuel) :
    powModK.window b m k fuel e = b ^ e % m := by
  induction fuel generalizing e with
  | zero => omega
  | succ fuel ih =>
    change (e.beq 0).rec
      (((powModK.window b m k fuel (e / k)) ^ k * b ^ (e % k)) % m)
      (1 % m) = b ^ e % m
    simp only [Bool.rec_eq, beq_eq]
    split
    next he => simp [he]
    next he =>
      have hdiv : e / k < fuel := Nat.lt_of_lt_of_le
        (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by omega)) (by omega)
      rw [ih _ hdiv, Nat.mul_mod, ← Nat.pow_mod, ← Nat.pow_mul,
        ← Nat.mul_mod, ← Nat.pow_add, Nat.div_add_mod']

-- TODO: once a published Lean toolchain containing leanprover/lean4#15167 is
-- supported here, remove the local window/dispatch implementation and use
-- `Nat.powMod` and `Nat.powMod_def`. Preserve the `powModK` API and helper lemmas.

/-- Kernel-reducible modular exponentiation: computes `a ^ b % n`.
Uses six-, four-, three-, and two-bit windows through moduli `2^64`, `2^512`,
`2^1024`, and `2^2048`. Above that, reduced bases below `2^64` use two-bit
windows through `2^4096`, then one-bit windows. Other inputs use the binary
accumulator. Modulus zero retains `a ^ b`. -/
@[expose] public noncomputable def powModK (a b n : Nat) : Nat :=
  (b.beq 0).rec
    ((n.ble ((1 : Nat).shiftLeft 1024)).rec
      ((n.ble ((1 : Nat).shiftLeft 2048)).rec
        (((a.mod n).ble 18446744073709551615).rec
          (aux b.succ (a.mod n) b 1)
          ((n.ble ((1 : Nat).shiftLeft 4096)).rec
            (powModK.window (a.mod n) n 2 b.succ b)
            (powModK.window (a.mod n) n 4 b.succ b)))
        (powModK.window (a.mod n) n 4 b.succ b))
      ((n.ble ((1 : Nat).shiftLeft 512)).rec
        (powModK.window (a.mod n) n 8 b.succ b)
        ((n.ble ((1 : Nat).shiftLeft 64)).rec
          (powModK.window (a.mod n) n 16 b.succ b)
          (powModK.window (a.mod n) n 64 b.succ b))))
    ((1 : Nat).mod n)
where
  aux : Nat → ((a b c : Nat) → Nat) :=
    Nat.rec (fun _ _ _ => 0)
      (fun _ r a b c =>
        (b.beq 0).rec
          (((b.mod 2).beq 0).rec
            (r ((a.mul a).mod n) (b.div 2) ((a.mul c).mod n))
            (r ((a.mul a).mod n) (b.div 2) c))
          (c.mod n))

/-- Computable version of `powModK` using `partial_fixpoint`. Used at elaboration time
(e.g. in `mkPowModEq'`) where we need actual computation, not kernel reduction. -/
public def powMod (a b n : ℕ) : ℕ :=
  aux (a % n) b 1
  where aux (a b c : ℕ) : ℕ :=
    if b = 0 then c % n
    else if b = 1 then (a * c) % n
    else if b % 2 = 0 then
      aux (a * a % n) (b / 2) c
    else
      aux (a * a % n) (b / 2) (a * c % n)
    partial_fixpoint

@[simp] lemma powModK_aux_zero_eq {n a b c : ℕ} :
    powModK.aux n 0 a b c = 0 := rfl

lemma powModK_aux_succ_eq {n a b c fuel : ℕ} :
    powModK.aux n (fuel + 1) a b c =
      (b.beq 0).rec (true := c % n)
      (((b % 2).beq 0).rec
        (powModK.aux n fuel (a * a % n) (b / 2) (a * c % n))
        (powModK.aux n fuel (a * a % n) (b / 2) c)) := by
  rfl

lemma powModK_aux_succ_eq' {n a b c fuel : ℕ} :
    powModK.aux n (fuel + 1) a b c =
      if b = 0 then c % n else
      if b % 2 = 0 then powModK.aux n fuel (a * a % n) (b / 2) c
      else powModK.aux n fuel (a * a % n) (b / 2) (a * c % n) := by
  simp only [powModK_aux_succ_eq, Bool.rec_eq, beq_eq]

lemma powModK_aux_eq (n a b c fuel) (hfuel : b < fuel) :
    powModK.aux n fuel a b c = powModAux a b c n := by
  induction fuel generalizing a b c with
  | zero => omega
  | succ fuel ih =>
    rw [powModK_aux_succ_eq']
    split
    case isTrue hb0 => rw [hb0, powModAux, pow_zero, one_mul]
    split
    case isTrue hb0 hbe =>
      rw [ih _ _ _ (by omega)]
      rw [powModAux, powModAux, Nat.mul_mod _ c, Nat.mul_mod _ c]
      conv_rhs =>
        rw [← Nat.mod_add_div b 2]
      rw [hbe, zero_add, pow_mul, ← pow_two, ← Nat.pow_mod]
    case isFalse hb0 hbo =>
      rw [ih _ _ _ (by omega)]
      rw [powModAux, powModAux, Nat.mul_mod, Nat.mod_mod, ← pow_two,
        ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.mul_mod, ← mul_assoc, ← Nat.pow_add_one]
      congr! 3
      lia

public lemma powModK_eq (a b n : ℕ) : powModK a b n = a ^ b % n := by
  simp only [powModK, Bool.rec_eq, beq_eq]
  split
  next hb => subst b; rfl
  next =>
    repeat' split
    all_goals first
      | rw [powModK.window_eq _ _ _ _ _ (by decide) (by omega)]
        exact (Nat.pow_mod a b n).symm
      | rw [powModK_aux_eq _ _ _ _ _ (by omega)]
        rw [powModAux, mul_one, mod_eq_mod, ← Nat.pow_mod]


public lemma powMod_eq_of_powModK (a b n m : ℕ) (h : (powModK a b n).beq m) :
    a ^ b % n = m := by
  rwa [powModK_eq, beq_eq] at h

public lemma powMod_ne_of_powModK (a b n m : ℕ) (h : (powModK a b n).beq m = false) :
    a ^ b % n ≠ m := by
  have := Nat.ne_of_beq_eq_false h
  rwa [powModK_eq] at this
