/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.Sieve

/-! # What a mask's set bits are

The skip argument rests on a mask and the finished window sharing no bit, and the certificate
delivers that as a statement about values: no live value is a multiple of a skipped divisor. To
join the two, a bit of the mask has to be known to stand for a multiple. That is the direction
below, and it is the one the argument needs: every bit `buildMaskK` sets is a genuine multiple, so
a window bit whose value is not a multiple cannot be in the mask.

`buildMaskK p M A B n` starts from the two bits `A` and `B` and, while the shift still fits under
`M`, doubles the set by `lor`ing in a copy displaced by `p * 2 ^ (i + 1)`. Every displacement is an
even multiple of `p`, so each step keeps the set inside the two arithmetic progressions `A + 2p·t`
and `B + 2p·t`. The cutoff only ever drops a copy, so it costs the proof nothing.

Written against `PrimeCert.Sieve` alone, which this box can compile, rather than against
`PrimeCert/SegmentedSieve.lean`, which it cannot. -/

namespace PrimeCert.SegTune.MaskBitProbe

open PrimeCert.Sieve

/-- A single shifted bit is set at one index and no other. The same statement as the copy in
`ChunkProductProbe`, repeated because that file imports nothing on purpose. -/
public theorem eq_of_testBit_one_shiftLeft {p i : Nat}
    (h : Nat.testBit (Nat.shiftLeft 1 p) i = true) : i = p := by
  -- The definitions here spell the operation `Nat.shiftLeft`, core states its lemmas with `<<<`,
  -- and `rw` matches syntactically, so the notation has to be put on first.
  change Nat.testBit (1 <<< p) i = true at h
  rw [Nat.testBit_shiftLeft] at h
  simp at h
  have h2 : ∀ m, Nat.testBit 1 m = true → m = 0 := by
    intro m hm
    cases m with
    | zero => rfl
    | succ n =>
      rw [Nat.testBit_succ] at hm
      simp at hm
  have := h2 _ h.2
  omega

/-- Every bit of the mask sits on one of the two progressions the seeds generate under
displacement by `2p`. -/
public theorem testBit_buildMaskK (p M A B : Nat) :
    ∀ n i, Nat.testBit (buildMaskK p M A B n) i = true →
      ∃ t, i = A + 2 * p * t ∨ i = B + 2 * p * t := by
  intro n
  induction n with
  | zero =>
    intro i hb
    have h0 : buildMaskK p M A B 0 = Nat.lor (Nat.shiftLeft 1 A) (Nat.shiftLeft 1 B) := rfl
    rw [h0] at hb
    change Nat.testBit (Nat.shiftLeft 1 A ||| Nat.shiftLeft 1 B) i = true at hb
    rw [Nat.testBit_or] at hb
    refine ⟨0, ?_⟩
    cases h1 : Nat.testBit (Nat.shiftLeft 1 A) i with
    | true =>
      refine Or.inl ?_
      rw [eq_of_testBit_one_shiftLeft h1]
      omega
    | false =>
      rw [h1, Bool.false_or] at hb
      refine Or.inr ?_
      rw [eq_of_testBit_one_shiftLeft hb]
      omega
  | succ k ih =>
    intro i hb
    have hs : buildMaskK p M A B (k + 1)
        = ((p.shiftLeft k.succ).ble M).rec (buildMaskK p M A B k)
          (Nat.lor (buildMaskK p M A B k)
            (Nat.shiftLeft (buildMaskK p M A B k) (p.shiftLeft k.succ))) := rfl
    rw [hs] at hb
    cases hble : Nat.ble (p.shiftLeft k.succ) M with
    | false =>
      rw [hble] at hb
      exact ih i hb
    | true =>
      rw [hble] at hb
      dsimp only at hb
      change Nat.testBit (buildMaskK p M A B k |||
        Nat.shiftLeft (buildMaskK p M A B k) (p.shiftLeft k.succ)) i = true at hb
      rw [Nat.testBit_or] at hb
      cases h1 : Nat.testBit (buildMaskK p M A B k) i with
      | true => exact ih i h1
      | false =>
        rw [h1, Bool.false_or] at hb
        change Nat.testBit (buildMaskK p M A B k <<< p.shiftLeft k.succ) i = true at hb
        rw [Nat.testBit_shiftLeft] at hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨hge, hbit⟩ := hb
        obtain ⟨t, ht⟩ := ih _ hbit
        -- The displacement is `p * 2 ^ (k + 1)`, which is `2p` times `2 ^ k`, so a displaced copy
        -- stays on the same progression with `t` advanced rather than starting a new one.
        have hsh : p.shiftLeft k.succ = 2 * p * 2 ^ k := by
          change p <<< k.succ = 2 * p * 2 ^ k
          rw [Nat.shiftLeft_eq, Nat.pow_succ]
          simp only [Nat.mul_comm, Nat.mul_assoc]
        rw [hsh] at hge ht
        have hkey : i = i - 2 * p * 2 ^ k + 2 * p * 2 ^ k := (Nat.sub_add_cancel hge).symm
        refine ⟨t + 2 ^ k, ?_⟩
        cases ht with
        | inl h =>
          refine Or.inl ?_
          rw [h] at hkey
          rw [hkey, Nat.mul_add, Nat.add_assoc]
        | inr h =>
          refine Or.inr ?_
          rw [h] at hkey
          rw [hkey, Nat.mul_add, Nat.add_assoc]

/-! ## From the progression to divisibility

A progression on indices is a progression on values: stepping the index by two steps the value by
six, because `valueK k` is `3k + 1 + k % 2` and an even step leaves the parity alone. Six steps of
`p` keep `p` a divisor, so once a seed's value is a multiple of `p` every bit the mask sets names a
multiple of `p` — which is what makes a gcd of 1 enough to drop the divisor. -/

/-- An even step on the index is six times that step on the value. The parity term is what makes
this worth stating: `valueK` is not linear, and this is exactly where its nonlinearity cancels. -/
public theorem valueK_add_two_mul (A d : Nat) : valueK (A + 2 * d) = valueK A + 6 * d := by
  change (A + 2 * d) * 3 + 1 + (A + 2 * d) % 2 = A * 3 + 1 + A % 2 + 6 * d
  rw [Nat.add_mul_mod_self_left]
  omega

/-- Every index on a seed's progression names a multiple of `p`, given the seed does. -/
public theorem dvd_valueK_of_progression {p A t : Nat} (h : p ∣ valueK A) :
    p ∣ valueK (A + 2 * (p * t)) := by
  rw [valueK_add_two_mul]
  refine Nat.dvd_add h ⟨6 * t, ?_⟩
  simp only [Nat.mul_comm, Nat.mul_assoc]

/-- The two put together: every bit the mask sets names a multiple of `p`, given both seeds do.
This is the statement the skip argument consumes — a window bit whose value `p` does not divide
cannot be a bit of `p`'s mask, so a divisor whose mask misses the finished window may be dropped
without the kernel ever walking the mask. -/
public theorem dvd_valueK_of_testBit_buildMaskK {p M A B n i : Nat}
    (hA : p ∣ valueK A) (hB : p ∣ valueK B)
    (h : Nat.testBit (buildMaskK p M A B n) i = true) : p ∣ valueK i := by
  obtain ⟨t, ht⟩ := testBit_buildMaskK p M A B n i h
  have hassoc : ∀ C : Nat, C + 2 * p * t = C + 2 * (p * t) := by
    intro C
    rw [Nat.mul_assoc]
  cases ht with
  | inl hl =>
    rw [hl, hassoc]
    exact dvd_valueK_of_progression hA
  | inr hr =>
    rw [hr, hassoc]
    exact dvd_valueK_of_progression hB

/-! ## The seeds the sieve actually uses

`segMarkK` seeds the mask with the indices of `5p` and `7p`, so the hypotheses above are met by
`rfl` whenever `valueK (indexK (5p))` really is `5p`. That holds when `p` is coprime to 6, which
every divisor the sieve scans is, and the two checks below are the shape of that argument at a
concrete `p`. Proving it for all coprime `p` is the next step and wants no new machinery. -/

/-- Indexing and valuing are inverse on the numbers coprime to 6, which is what makes the seeds
name `5p` and `7p` rather than whatever lies nearest. Stated by the residue rather than by
`Nat.Coprime`, so that it needs core only and `omega` can see the division. -/
public theorem valueK_indexK (q : Nat) (h : q % 6 = 1 ∨ q % 6 = 5) : valueK (indexK q) = q := by
  change (q - 1) / 3 * 3 + 1 + (q - 1) / 3 % 2 = q
  omega

/-- The first seed names a multiple of `p`, for any `p` coprime to 6. -/
public theorem dvd_valueK_seed_five {p : Nat} (h : p % 6 = 1 ∨ p % 6 = 5) :
    p ∣ valueK (indexK (p * 5)) := by
  rw [valueK_indexK _ (by omega)]
  exact ⟨5, rfl⟩

/-- The second seed names a multiple of `p`, for any `p` coprime to 6. -/
public theorem dvd_valueK_seed_seven {p : Nat} (h : p % 6 = 1 ∨ p % 6 = 5) :
    p ∣ valueK (indexK (p * 7)) := by
  rw [valueK_indexK _ (by omega)]
  exact ⟨7, rfl⟩

/-- Both hypotheses discharged from the residue alone: every bit of `p`'s mask names a multiple of
`p`, for every `p` the sieve scans. -/
public theorem dvd_valueK_of_testBit_mask {p M n i : Nat} (hp : p % 6 = 1 ∨ p % 6 = 5)
    (h : Nat.testBit (buildMaskK p M (indexK (p * 5)) (indexK (p * 7)) n) i = true) :
    p ∣ valueK i :=
  dvd_valueK_of_testBit_buildMaskK (dvd_valueK_seed_five hp) (dvd_valueK_seed_seven hp) h

example : valueK (indexK (5 * 5)) = 25 := rfl
example : valueK (indexK (5 * 7)) = 35 := rfl

/-! ## The window's own seeds

A segment's mask is not seeded with `indexK (5p)` itself but with `firstLocK (indexK (5p)) lo 2p`,
the first offset inside the window that lands in the same class modulo `2p`. So the bits are local
offsets and the value at offset `i` is `valueK (lo + i)`, which the lemmas above do not reach.

What closes the distance is that `valueK` only cares about the index modulo `2p`, as far as `p`
dividing it goes: an even step on the index is six times that step on the value, so a whole turn of
`2p` adds `6p`. Hence divisibility can be read off the residue, and `firstLocK` was built to put
`lo + i` in the right residue. -/

/-- Reducing the index modulo `2p` leaves `valueK` the same up to a multiple of `p`. -/
public theorem valueK_eq_mod (p x : Nat) :
    valueK x = valueK (x % (2 * p)) + 6 * (p * (x / (2 * p))) := by
  have hassoc : 2 * p * (x / (2 * p)) = 2 * (p * (x / (2 * p))) := Nat.mul_assoc 2 p _
  have hx : x = x % (2 * p) + 2 * (p * (x / (2 * p))) := by
    rw [← hassoc]
    exact (Nat.mod_add_div x (2 * p)).symm
  calc valueK x = valueK (x % (2 * p) + 2 * (p * (x / (2 * p)))) := by rw [← hx]
    _ = valueK (x % (2 * p)) + 6 * (p * (x / (2 * p))) := valueK_add_two_mul _ _

/-- So `p` divides a value exactly when it divides the value of the reduced index. -/
public theorem dvd_valueK_iff_mod (p x : Nat) : p ∣ valueK x ↔ p ∣ valueK (x % (2 * p)) := by
  have hd : p ∣ 6 * (p * (x / (2 * p))) := ⟨6 * (x / (2 * p)), by
    simp only [Nat.mul_comm, Nat.mul_assoc]⟩
  rw [valueK_eq_mod p x]
  constructor
  · intro h
    rw [Nat.add_comm] at h
    exact (Nat.dvd_add_right hd).mp h
  · intro h
    exact Nat.dvd_add h hd

/-- Local copy of `firstLocK`, which lives in `PrimeCert/SegmentedSieve.lean` and so is out of
reach here. Same arithmetic, so the two are `rfl` when this moves across. -/
@[expose] public def firstLocK (A lo m : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add A m) (Nat.mod lo m)) m

/-- `firstLocK` does what its name says: the offset it returns puts `lo + it` in `A`'s class. -/
public theorem firstLocK_mod (A lo m : Nat) (hm : 0 < m) :
    (lo + firstLocK A lo m) % m = A % m := by
  have hle : lo % m ≤ A + m :=
    Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ hm)) (Nat.le_add_left m A)
  change (lo + (A + m - lo % m) % m) % m = A % m
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod, Nat.add_sub_cancel' hle, Nat.add_mod_right]

-- Composed at a concrete divisor: any bit of 5's mask names a multiple of 5, and the two seed
-- hypotheses are discharged by reduction.
example (i : Nat) (h : Nat.testBit (buildMaskK 5 40 (indexK 25) (indexK 35) 3) i = true) :
    5 ∣ valueK i :=
  dvd_valueK_of_testBit_buildMaskK ⟨5, rfl⟩ ⟨7, rfl⟩ h

/-- The segment's own statement, and the one the skip argument wants: every bit a window mask sets
names a multiple of `p`, where the value at local offset `i` is `valueK (lo + i)`.

So if a divisor's mask and the finished window share a bit, that bit's value is both live and a
multiple of the divisor. The certificate rules the second out by a gcd, so the masks of the skipped
divisors meet the window in nothing, and they may be dropped. -/
public theorem dvd_valueK_of_testBit_segMask {p M lo n i : Nat} (hp : p % 6 = 1 ∨ p % 6 = 5)
    (hpos : 0 < p)
    (h : Nat.testBit (buildMaskK p M (firstLocK (indexK (p * 5)) lo (p * 2))
      (firstLocK (indexK (p * 7)) lo (p * 2)) n) i = true) :
    p ∣ valueK (lo + i) := by
  have hm : p * 2 = 2 * p := Nat.mul_comm p 2
  obtain ⟨t, ht⟩ := testBit_buildMaskK p M _ _ n i h
  have hstep : ∀ A : Nat, p ∣ valueK A →
      p ∣ valueK (lo + (firstLocK A lo (p * 2) + 2 * p * t)) := by
    intro A hA
    have hassoc : lo + (firstLocK A lo (p * 2) + 2 * p * t)
        = lo + firstLocK A lo (p * 2) + 2 * (p * t) := by
      rw [Nat.mul_assoc]
      omega
    rw [hassoc]
    refine dvd_valueK_of_progression ?_
    rw [dvd_valueK_iff_mod, ← hm, firstLocK_mod A lo (p * 2) (by omega), hm,
      ← dvd_valueK_iff_mod]
    exact hA
  cases ht with
  | inl hl =>
    rw [hl]
    exact hstep _ (dvd_valueK_seed_five hp)
  | inr hr =>
    rw [hr]
    exact hstep _ (dvd_valueK_seed_seven hp)

end PrimeCert.SegTune.MaskBitProbe
