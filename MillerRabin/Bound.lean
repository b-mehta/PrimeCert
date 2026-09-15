/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import MillerRabin.Defs
public import PrimeCert.SieveCorrect
public import PrimeCert.ForallB

/-! # The Wieferich condition along a residue class of a sieve

`wieferichAtK s` reads the condition at one position of the sieve `s`, with `wieferichAtK_iff` as
its specification. `not_wieferich_of_fold` and `not_wieferich_of_fold_offset` turn a scan of one
residue class into the statement that a prime of that class fails the condition.
-/

namespace MillerRabin

open PrimeCert PrimeCert.Sieve

/-- The Wieferich check at position `t` of the sieve `s`: true when the bit at `t` is clear, or
when the number at `t` fails `Wieferich`. -/
@[expose] public noncomputable def wieferichAtK (s t : ℕ) : Bool :=
  (testBitK s t).not'.or' (wieferichK (valueK t)).not'

/-- The check holds exactly when the bit is clear or the number there fails `Wieferich`. -/
@[simp, grind =] public theorem wieferichAtK_iff {s t : ℕ} :
    wieferichAtK s t ↔ ¬ s.testBit t ∨ ¬ wieferichK (value t) := by
  grind [wieferichAtK, Bool.not'_eq_not, Bool.or'_eq_or]

/-- Read the value at one member of a class from a scan starting at position `j` of that class,
whose successive members sit `d` indices apart. -/
public theorem eval_of_offset {f : ℕ → Bool} {r m d j k len : ℕ}
    (hr : r.Coprime 6) (hm : m % 6 = 0) (hd : m / 3 = d) (hj : j ≤ k)
    (hk : k - j < len) (hfold : forallB f (index r + d * j) len d) :
    f (index (r + m * k)) := by
  subst hd
  obtain ⟨c, rfl⟩ : ∃ c, m = 6 * c := ⟨m / 6, by lia⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h3 : 6 * c / 3 = 2 * c := by lia
  rw [h3] at hfold
  have := (forallB_iff f _ len _).mp hfold e (by simpa using hk)
  rw [mul_assoc, index_add hr]
  convert this using 2
  ring

/-- Read the value at one member of a class off that class's scan. -/
public theorem eval_of_class {f : ℕ → Bool} {r m k len : ℕ} (hr : r.Coprime 6)
    (hm : m % 6 = 0) (hk : k < len) (hfold : forallB f (index r) len (m / 3)) :
    f (index (r + m * k)) :=
  eval_of_offset (j := 0) (len := len) hr hm rfl (Nat.zero_le k) (by lia) (by simpa using hfold)

/-- At a prime whose check holds, the Wieferich condition fails. -/
public theorem not_wieferich_of_check {n s p : ℕ} (hs : IsSieve n s) (hp : p.Prime)
    (hb : p ≤ n) (hc : p.Coprime 6) (h : wieferichAtK s (index p)) :
    ¬ Wieferich p := by
  have hbit := hs.testBit_of_prime hp hb hc
  have hnum : value (index p) = p := value_index hc
  grind [wieferichK_eq_false_iff, hp.ne_one]

/-- A prime whose class is covered by a scan fails the Wieferich condition. -/
public theorem not_wieferich_of_fold {n s p m len : ℕ} (hs : IsSieve n s) (hp : p.Prime)
    (hb : p ≤ n) (hm : m % 6 = 0) (hc : p.Coprime 6) (hk : p / m < len)
    (hfold : forallB (wieferichAtK s) (index (p % m)) len (m / 3)) : ¬ Wieferich p := by
  have hmod : p % m % 6 = p % 6 := Nat.mod_mod_of_dvd p (Nat.dvd_of_mod_eq_zero hm)
  have hr : (p % m).Coprime 6 := by rwa [coprime6_mod, hmod, ← coprime6_mod]
  refine not_wieferich_of_check hs hp hb hc ?_
  have := eval_of_class (k := p / m) hr hm hk hfold
  rwa [Nat.mod_add_div] at this

/-- A prime covered by a scan that starts at position `j` of its class fails the Wieferich
condition. -/
public theorem not_wieferich_of_fold_offset {n s p m d j len : ℕ} (hs : IsSieve n s)
    (hp : p.Prime) (hb : p ≤ n) (hm : m % 6 = 0) (hc : p.Coprime 6) (hd : m / 3 = d)
    (hj : j ≤ p / m) (hk : p / m - j < len)
    (hfold : forallB (wieferichAtK s) (index (p % m) + d * j) len d) : ¬ Wieferich p := by
  have hmod : p % m % 6 = p % 6 := Nat.mod_mod_of_dvd p (Nat.dvd_of_mod_eq_zero hm)
  have hr : (p % m).Coprime 6 := by rwa [coprime6_mod, hmod, ← coprime6_mod]
  refine not_wieferich_of_check hs hp hb hc ?_
  have := eval_of_offset (k := p / m) hr hm hd hj hk hfold
  rwa [Nat.mod_add_div] at this

end MillerRabin
