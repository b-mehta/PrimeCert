/-
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta, Kim Morrison
-/

module

import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.ModEq
import PrimeCert.ForMathlib
public import PrimeCert.ForallB
public import PrimeCert.Pocklington

/-! # Pocklington's primality test, cube-root variant

The classic Pocklington test requires factoring a divisor `F > √N` of `N - 1`.
This variant (due to Brillhart–Lehmer–Selfridge) only needs `F > N^(1/3)`, at the cost of
an additional divisibility sieve up to a small bound `m` and a non-square check on `r² - 8s`
(where `R = (N-1)/F` and `R = 2·F·s + r`).
-/

/-- `Nat.modEq_iff_exists_eq_add` reshaped into the `k * b + q = p` form that
`pocklington3_test` consumes directly. -/
theorem Nat.modEq_iff_exists_mul_add' {p q b : ℕ} (hqp : q ≤ p) :
    p ≡ q [MOD b] ↔ ∃ k, k * b + q = p := by
  rw [ModEq.comm, modEq_iff_dvd' hqp]
  rw [le_iff_exists_add'] at hqp
  obtain ⟨c, rfl⟩ := hqp
  simp_rw [add_tsub_cancel_right, add_left_inj, dvd_iff_exists_eq_mul_left, eq_comm]

namespace PrimeCert

/-- The smallest `m ≥ 1` with `2s + m² < (2F + r)·m + 2` (the `pock3` bound condition), or `0`
if no such `m` exists — which indicates `F` is too small for a valid certificate.

Writing `b := 2F + r`, the condition is `m² - b·m + (2s - 2) < 0`, satisfied on the open interval
between the roots of that quadratic. A solution exists iff the discriminant `b² - 8s + 8` is
positive, and the least one sits just above the lower root `(b - √(b² - 8s + 8)) / 2`. So we
compute it directly with an integer square root and confirm against a tiny window, rather than
scanning — the failure case (`F` too small) returns at once instead of iterating. -/
public def minimalSieveBound (twoF r s : ℕ) : ℕ :=
  let b := twoF + r
  if b * b + 8 ≤ 8 * s then 0
  else Id.run do
    let sq := Nat.sqrt (b * b + 8 - 8 * s)
    let cand := (b - sq) / 2
    for m in [max 1 (cand - 3) : cand + 4] do
      if 2 * s + m * m < b * m + 2 then return m
    return 0


/-- The non-square certificate: one of three conditions that rule out `r² - 8s` being a
perfect square, which is needed to exclude composite factorisations. -/
def Pocklington3Cert (r s : ℕ) : Prop :=
  s = 0 ∨ ¬ IsSquare (r ^ 2 - 8 * s) ∨ r ^ 2 < 8 * s

theorem pocklington3_test (N F R m r s : ℕ)
    (R_def : F * R + 1 = N) (r_def : R % (2 * F) = r) (s_def : R / (2 * F) = s)
    (h2n : 2 ≤ N) (odd_n : Odd N) (odd_R : Odd R)
    (primitive : ∀ p ∈ F.primeFactors, ∃ a, a ^ (N - 1) ≡ 1 [MOD N] ∧
      (a ^ ((N - 1) / p) - 1).gcd N = 1)
    (divisors : ∀ l, 1 ≤ l → l < m → ¬ l * F + 1 ∣ N)
    (bound : N + (m * F + 1) * (m * F) < (m * F + 1) * (2 * F ^ 2 + r * F + 1))
    (cert : s = 0 ∨ ¬ IsSquare (r ^ 2 - 8 * s) ∨ r ^ 2 < 8 * s) :
    Nat.Prime N := by
  simp_rw [Nat.prime_iff_not_exists_mul_eq', not_exists, not_and]
  refine ⟨by lia, fun p q h2p hpn h2q hqn hpq ↦ ?_⟩
  have := pocklington_test N F (by lia)
    (by rw [← R_def, Nat.add_sub_cancel_right]; exact dvd_mul_right _ _) primitive
  replace this := Nat.modEq_one_of_dvd_of_prime _ _ this
  have hp := this p (hpq ▸ dvd_mul_right _ _)
  have hq := this q (hpq ▸ dvd_mul_left _ _)
  rw [Nat.modEq_iff_exists_mul_add' (by lia)] at hp hq
  obtain ⟨c, rfl⟩ := hp
  obtain ⟨d, rfl⟩ := hq
  have hmc : m ≤ c := le_of_not_gt fun hcm ↦ by
    obtain hc | hc := le_or_gt 1 c
    · exact divisors c hc hcm (hpq ▸ dvd_mul_right _ _)
    · interval_cases c; rw [zero_mul] at h2p; lia
  have hmd : m ≤ d := le_of_not_gt fun hdm ↦ by
    obtain hd | hd := le_or_gt 1 d
    · exact divisors d hd hdm (hpq ▸ dvd_mul_left _ _)
    · interval_cases d; rw [zero_mul] at h2q; lia
  have hf₀ : F ≠ 0 := by rintro rfl; rw [zero_mul] at R_def; lia
  have hR₂ := Nat.div_add_mod R (2 * F)
  rw [r_def, s_def] at hR₂
  rw [show (c * F + 1) * (d * F + 1) = F * ((c * d) * F + (c + d)) + 1 by ring,
    ← R_def, add_left_inj, Nat.mul_right_inj hf₀] at hpq
  have even_F : Even F := by
    rw [← R_def, Nat.odd_add_one, Nat.not_odd_iff_even, Nat.even_mul] at odd_n
    exact odd_n.resolve_right (Nat.not_even_iff_odd.mpr odd_R)
  have odd_cd : Odd (c + d) := by
    rw [← hpq] at odd_R
    refine (Nat.odd_add'.mp odd_R).mpr <| Even.mul_left even_F _
  have even_cd : Even (c * d) := by
    rw [Nat.odd_add, ← Nat.not_even_iff_odd] at odd_cd
    rw [Nat.even_mul]; exact (em (Even c)).imp id odd_cd.mp
  have hcdr : (c + d) % (2 * F) = r := by
    obtain ⟨q, hq⟩ := even_iff_exists_two_mul.mp even_cd
    replace hpq := congr($hpq % (2 * F))
    rwa [hq, mul_right_comm, Nat.mul_add_mod, r_def] at hpq
  have hcdm : (c + d) * m ≤ c * d + m ^ 2 := by
    rw [add_mul]
    obtain ⟨c, hc⟩ := le_iff_exists_add.mp hmc
    obtain ⟨d, hd⟩ := le_iff_exists_add.mp hmd
    rw [hc, hd]
    lia
  have hcdr₁ : c + d < 2 * F + r := by
    rw [← R_def, ← hpq] at bound
    conv_lhs at bound => exact
      show _ = (c * d + m ^ 2) * F ^ 2 + (c + d) * F + (m * F + 1) by ring
    grw [← hcdm] at bound
    conv_lhs at bound => exact show _ = (m * F + 1) * ((c + d) * F + 1) by ring
    rw [mul_lt_mul_iff_right₀ (by lia), add_lt_add_iff_right] at bound
    conv_rhs at bound => exact show _ = (2 * F + r) * F by ring
    rwa [mul_lt_mul_iff_left₀ (by lia)] at bound
  have hcdr₂ := Nat.div_add_mod (c + d) (2 * F)
  rw [hcdr] at hcdr₂
  rw [← hcdr₂, add_lt_add_iff_right, mul_lt_iff_lt_one_right (by lia), Nat.lt_one_iff] at hcdr₁
  rw [hcdr₁, mul_zero, zero_add] at hcdr₂
  have hscd := hR₂.trans hpq.symm
  rw [← hcdr₂, add_left_inj, mul_right_comm, mul_left_inj' (by lia)] at hscd
  obtain cert | cert := cert
  · -- first case: s = 0
    rw [cert, mul_zero, eq_comm, mul_eq_zero] at hscd
    lia
  · -- second case: r^2-8s is not square
    have square : r ^ 2 = 8 * s + (max c d - min c d) ^ 2 := by
      rw [hcdr₂, show 8 = 4 * 2 by rfl, mul_assoc, hscd, Nat.add_sq_eq_dist_sq_add_four_mul,
        add_comm]
    rw [square, Nat.add_sub_cancel_left] at cert
    obtain cert | cert := cert
    · exact cert ⟨_, sq _⟩
    · lia

/-- An integer strictly between consecutive squares cannot be a square. -/
theorem Pocklington3Cert.of_interval (r s w : Nat)
    (lo : w * w < r ^ 2 - 8 * s) (hi : r ^ 2 - 8 * s < (w + 1) * (w + 1)) :
    Pocklington3Cert r s := by
  exact .inr <| .inl fun ⟨a, ha⟩ ↦ Nat.not_exists_sq lo hi ⟨a, ha.symm⟩

/-- How to discharge the `Pocklington3Cert` obligation:
- `zero`: `s = 0`
- `lt`: `r² < 8s`
- `interval w`: `w² < r² - 8s < (w+1)²` -/
public inductive Pocklington3CertMode : Type
  | zero | lt | interval (w : ℕ)

@[expose] public noncomputable def Pocklington3CertMode.calculate (m : Pocklington3CertMode)
    (r s : ℕ) : Bool :=
  m.rec (s.beq 0) (r.pow 2 |>.blt <| s.mul 8)
    (fun w ↦
      let d := r.pow 2 |>.sub <| s.mul 8
      (w.mul w |>.blt d) && (d.blt (w.succ.mul w.succ)))

theorem Pocklington3CertMode.to_cert (m : Pocklington3CertMode) (r s : ℕ) (h : m.calculate r s) :
    Pocklington3Cert r s := by
  cases m with
  | zero => exact .inl <| Nat.beq_eq.to_iff.mp h
  | lt => exact .inr <| .inr <| Nat.blt_eq.to_iff.mp <| mul_comm 8 s ▸ h
  | interval w =>
    simp only [calculate, Bool.and_eq_true, Nat.blt_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.sub_eq, Nat.succ_eq_add_one, mul_comm s 8] at h
    exact .of_interval r s w h.1 h.2

public structure PrimePow : Type where
  (prime : ℕ) (pow : ℕ) (pf : prime.Prime) (pow_ne_zero : (0).blt pow)

@[expose] public noncomputable def PrimePow.toNat (pp : PrimePow) : ℕ :=
  pp.rec fun p v _ _ ↦ p.pow v

@[simp] theorem PrimePow.toNat_def (pp : PrimePow) : pp.toNat = pp.prime ^ pp.pow := rfl

theorem PrimePow.prime_dvd_toNat (pp : PrimePow) : pp.prime ∣ pp.toNat :=
  dvd_pow_self _ <| ne_of_gt <| Nat.blt_eq.to_iff.mp pp.pow_ne_zero

@[expose] public noncomputable def pocklington3_calculate (N e root m : ℕ) (F' : List PrimePow)
    (mode : Pocklington3CertMode) : Bool :=
  let F := Nat.mul (F'.rec 1 fun pp _ ih ↦ pp.rec fun p vp _ _ ↦ ih.mul <| p.pow vp) <| (2).pow e
  let two_F := F.mul 2
  let R := N.div F
  let r := R.mod two_F
  let s := R.div two_F
  F'.rec (powModK root (N.div 2) N |>.pred.gcd N |>.beq 1)
    (fun pp _ ih ↦ pp.rec fun p _ _ _ ↦
      (powModK root (N.div p) N |>.pred.gcd N |>.beq 1).and' ih) &&
  (0).blt e &&
  (mode.calculate r s) &&
  (N.mod F |>.beq 1) &&
  (R.mod 2 |>.beq 1) &&
  (powModK root N.pred N |>.beq 1) &&
  (forallB (fun l ↦ Nat.blt 0 (N.mod l)) F.succ m.pred F) &&
  (s.mul 2 |>.add (m.pow 2) |>.blt (two_F.add r |>.mul m |>.add 2))

theorem mem_primeFactors_prod_toNat (L : List PrimePow) (p : ℕ) :
    p ∈ (L.map PrimePow.toNat |>.prod |>.primeFactors) → ∃ pp ∈ L, pp.prime = p := by
  induction L with
  | nil => simp
  | cons pp _ ih =>
    rw [List.map_cons, List.prod_cons, Nat.primeFactors_mul, List.exists_mem_cons_iff,
      Finset.mem_union, pp.toNat_def]
    · refine Or.imp ?_ ih
      · by_cases h0 : pp.pow = 0
        · rw [h0, pow_zero, Nat.primeFactors_one]; grind
        · rw [Nat.primeFactors_prime_pow h0 pp.pf]; grind
    · exact pow_ne_zero _ pp.pf.ne_zero
    · refine List.prod_ne_zero ?_
      rw [List.mem_map, not_exists]
      exact fun pp h ↦ absurd h.2 <| pow_ne_zero _ pp.pf.ne_zero

-- `omega` is >2x faster than `lia` here (57ms vs 148ms median over 5 runs)
theorem of_gcd_pred_mod_eq_one (a b : ℕ) (h : (a % b - 1).gcd b = 1)
    (hb : 2 ≤ b) : (a - 1).gcd b = 1 := by
  rwa [Nat.gcd_comm, Nat.gcd_def, if_neg (by omega), ← Nat.mod_sub_of_le]
  · by_cases h₀ : a % b = 0
    · rw [h₀, Nat.zero_sub, Nat.gcd_zero_left] at h; omega
    · omega

/--
Inputs (not all needed):
* `N`: the number to be certified as prime
* `F`: an even divisor of `N-1`, fully factored, to be given as a literal
* `F'`: the odd part of `F`, given in factorised form
* `e`: the exponent of `2` in `F`, so that `F = 2^e * F'`
* `R`: the quotient `(N-1)/F`, odd, given as a literal.
* `root`: a pseudo-primitive root (for `F`)
* `m`: an arbitrary number (`> 0`), which should be small for better performance.
* `s, r := divmod(R, 2*F)`, given as literals
-/
public theorem pocklington3_certK (N root m e : ℕ) (F' : List PrimePow)
    (mode : Pocklington3CertMode) (cert : pocklington3_calculate N e root m F' mode) :
    Nat.Prime N := by
  unfold pocklington3_calculate at cert
  extract_lets F two_F R r s at cert
  simp only [Nat.div_eq_div, powModK_eq, Nat.pred_eq_sub_one, Nat.mod_eq_mod, Nat.succ_eq_add_one,
    Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at cert
  obtain ⟨⟨⟨⟨⟨⟨⟨primitive, e_pos⟩, cert⟩, hnf⟩, odd_R⟩, psp⟩, divisors⟩, bound⟩ := cert
  have R_def : F * R + 1 = N := by
    rw [← Nat.div_add_mod N F, hnf]; rfl
  have even_F : Even F :=
    (Nat.even_pow.mpr ⟨even_two, e_pos.ne'⟩).mul_left _
  have odd_N : Odd N := by
    rw [← R_def, Nat.odd_add_one, Nat.not_odd_iff_even]
    exact even_F.mul_right _
  have F_def : F = (F'.map PrimePow.toNat).prod * 2 ^ e := by
    simp only [F, Nat.mul_eq, Nat.pow_eq]
    congr 1
    clear * - F'
    induction F' with
    | nil => rfl
    | cons h _ ih => simp only [ih, List.map_cons, List.prod_cons, mul_comm h.toNat]; rfl
  have hf₀ : F ≠ 0 := by
    rw [F_def]
    refine mul_ne_zero (List.prod_ne_zero ?_) (pow_ne_zero _ <| by decide)
    rw [List.mem_map, not_exists]
    exact fun pp h ↦ absurd (h.2) <| pow_ne_zero _ pp.pf.ne_zero
  have hf₂ : 2 ≤ F := by lia
  have hn₁ : N ≠ 1 := by
    rintro rfl
    rw [add_eq_right, mul_eq_zero] at R_def
    rw [R_def.resolve_left hf₀] at odd_R
    grind
  have hn₃ : 3 ≤ N := by grind
  have dvd_F_of_mem_F' (pp) (h : pp ∈ F') : pp.prime ∣ F := by
    rw [F_def]
    exact dvd_mul_of_dvd_left (dvd_trans pp.prime_dvd_toNat <| List.dvd_prod <|
      List.mem_map_of_mem h) _
  have h_two_F : two_F = 2 * F := mul_comm F 2
  have hrs : 2 * F * s + r = R := by
    rw [← Nat.div_add_mod R (2 * F), ← h_two_F]; rfl
  refine pocklington3_test N F R m r s R_def (mul_comm 2 F ▸ rfl) (mul_comm 2 F ▸ rfl)
    (by lia) odd_N (Nat.odd_iff.mpr odd_R) ?_ ?_ ?_ ?_
  · simp only [List.rec_and, Nat.beq_eq] at primitive
    rw [F_def, ← PrimePow.toNat_def ⟨2, e, Nat.prime_two, by simpa⟩, mul_comm, ← List.prod_cons,
      ← List.map_cons]
    refine fun p hp ↦ ⟨root, ?_, ?_⟩
    · rw [Nat.ModEq, Nat.one_mod_eq_one.mpr hn₁, psp]
    · obtain ⟨pp, hpp, rfl⟩ := mem_primeFactors_prod_toNat _ _ hp
      rw [List.mem_cons] at hpp
      refine of_gcd_pred_mod_eq_one _ _ ?_ (by lia)
      obtain rfl | hpp := hpp
      · convert primitive.1 using 5
        convert Nat.div_eq_sub_mod_div.symm
        exact (Nat.odd_iff.mp odd_N).symm
      · convert primitive.2 pp hpp using 5
        convert Nat.div_eq_sub_mod_div.symm
        rw [eq_comm, ← Nat.one_mod_eq_one.mpr pp.pf.ne_one, ← Nat.ModEq]
        refine Nat.ModEq.of_dvd (dvd_F_of_mem_F' _ hpp) ?_
        rw [Nat.ModEq, Nat.one_mod_eq_one.mpr (by lia), hnf]
  · rw [show F + 1 = 1 * F + 1 by simp, forallB_iff'] at divisors
    simp only [Nat.blt_eq, Nat.pos_iff_ne_zero, ne_eq, ← Nat.dvd_iff_mod_eq_zero] at divisors
    exact fun l hl₁ hl₂ ↦ divisors l hl₁ (by lia)
  · rw [← R_def, ← hrs]
    conv_lhs => exact show _ = ((s * 2 + m ^ 2) * F + r + m) * F + 1 by ring
    conv_rhs => exact show _ = (((F * 2 + r) * m + 2) * F + r + m) * F + 1 by ring
    gcongr 5
    exact bound
  · exact mode.to_cert _ _ cert

end PrimeCert

