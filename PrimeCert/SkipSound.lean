/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.SegmentedSieve

/-!
# Reading the record certificate

`segMarkK_eq_self_of_not_dvd` already says that a divisor ruled out at every live position leaves
the window alone, so its mask need never be built. Its last hypothesis is the one the wide-band
sweep cannot discharge by itself:

```
∀ j, j ≤ Wm1 → testBitK seg j = true → ¬ p ∣ valueK (lo + j)
```

The record certificate exists to supply it. This file reads what the certificate states — chunks
of sixteen-bit records, each with a product and the bits it assembles to, chained into a product
for the window and one for the skipped set, and a single gcd between them — and gives back that
hypothesis, one chunk at a time.

Everything about the masks themselves is already proved: `mask_iff` and `testBit_buildMaskK` in
`PrimeCert/SieveCorrect.lean` characterise exactly which indices a mask marks, and
`value_add_two_mul`, `value_startA` and `value_startB` are the arithmetic underneath them. Nothing
here repeats any of that.

What is new is only the record side, because `prodChunkK` and `asmChunkK` are new: a product over
records means nothing without a statement that the records are the window's live positions, and an
assembly means nothing without one that the values those positions name share no factor with the
skipped divisors.
-/

namespace PrimeCert.Sieve

/-- A single shifted bit is set at one index and no other. -/
public theorem eq_of_testBit_one_shiftLeft {p i : Nat}
    (h : Nat.testBit (Nat.shiftLeft 1 p) i = true) : i = p := by
  -- These definitions spell the operation `Nat.shiftLeft`, core states its lemmas with `<<<`, and
  -- `rw` matches syntactically, so the notation has to be put on first.
  change Nat.testBit (1 <<< p) i = true at h
  rw [Nat.testBit_shiftLeft] at h
  simp only [ge_iff_le, Bool.and_eq_true, decide_eq_true_eq] at h
  -- `1` has its only bit at index 0, so the shifted index has to be the shift itself.
  have h2 : ∀ m, Nat.testBit 1 m = true → m = 0 := by
    intro m hm
    cases m with
    | zero => rfl
    | succ n =>
      rw [Nat.testBit_succ] at hm
      simp at hm
  have := h2 _ h.2
  omega

/-- Any bit the chunk assembles to has its value dividing the chunk's product.

`dvd_prodChunkK` reaches a factor by slot number, which is the emitter's coordinate and nothing
the rest of the chain knows. What the chain has is a bit of the window, and this is the form that
takes one: the slot never appears. -/
public theorem dvd_prodChunkK_of_testBit (recs lo cnt : Nat) :
    ∀ d off i, Nat.testBit (asmChunkK recs cnt d off) i = true →
      valueK (Nat.add lo i) ∣ prodChunkK recs lo cnt d off := by
  intro d
  induction d with
  | zero =>
    intro off i hb
    have ha : asmChunkK recs cnt 0 off = (Nat.blt off cnt).rec 0
        (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight recs (Nat.mul off 16)) 65535)) := rfl
    have hp : prodChunkK recs lo cnt 0 off = (Nat.blt off cnt).rec 1
        (valueK (Nat.add lo (Nat.land (Nat.shiftRight recs (Nat.mul off 16)) 65535))) := rfl
    rw [ha] at hb
    rw [hp]
    cases hblt : Nat.blt off cnt with
    | false =>
      -- `cases` substitutes in the goal and not in a hypothesis, so `hb` is rewritten by hand.
      rw [hblt] at hb
      dsimp only at hb
      simp at hb
    | true =>
      rw [hblt] at hb
      dsimp only at hb
      exact (eq_of_testBit_one_shiftLeft hb) ▸ Nat.dvd_refl _
  | succ k ih =>
    intro off i hb
    have ha : asmChunkK recs cnt (k + 1) off = Nat.lor (asmChunkK recs cnt k off)
        (asmChunkK recs cnt k (Nat.add off (Nat.pow 2 k))) := rfl
    have hp : prodChunkK recs lo cnt (k + 1) off = Nat.mul (prodChunkK recs lo cnt k off)
        (prodChunkK recs lo cnt k (Nat.add off (Nat.pow 2 k))) := rfl
    rw [ha] at hb
    change Nat.testBit (asmChunkK recs cnt k off |||
      asmChunkK recs cnt k (Nat.add off (Nat.pow 2 k))) i = true at hb
    rw [Nat.testBit_or] at hb
    rw [hp]
    cases h1 : Nat.testBit (asmChunkK recs cnt k off) i with
    | true => exact Nat.dvd_mul_right_of_dvd (ih off i h1) _
    | false =>
      rw [h1, Bool.false_or] at hb
      exact Nat.dvd_mul_left_of_dvd (ih (Nat.add off (Nat.pow 2 k)) i hb) _

/-- Each factor of a checked product divides it, which is every chain step's content. The chain
composes by transitivity, which is the whole of how a leaf reaches the root. -/
public theorem dvd_of_mul_eq {a b c : Nat} (h : Nat.mul a b = c) : a ∣ c ∧ b ∣ c := by
  constructor
  · exact ⟨b, h.symm⟩
  · exact ⟨a, by rw [← h]; exact Nat.mul_comm a b⟩

/-- A bit of a skip chunk's assembly names a divisor that divides the skipped product. Without
this a divisor could be dropped from the marking and left out of the product, and the gcd would
come back 1 for the wrong reason. -/
public theorem dvd_skipProd_of_testBit {recs lo cnt chunkProd skipProd i d : Nat}
    (hchunk : prodChunkK recs lo cnt d 0 = chunkProd) (hdvd : chunkProd ∣ skipProd)
    (hi : Nat.testBit (asmChunkK recs cnt d 0) i = true) : valueK (Nat.add lo i) ∣ skipProd := by
  refine Nat.dvd_trans ?_ hdvd
  rw [← hchunk]
  exact dvd_prodChunkK_of_testBit recs lo cnt d 0 i hi

/-- What the certificate says, in one statement: a divisor the skipped set names does not divide a
value the window names.

Every hypothesis is something the emitter states and the kernel checks, except the two
divisibilities, which the multiplication chains supply a step at a time, and `hne`, which holds
because 1 is not a divisor the sieve ever skips. This is the shape
`segMarkK_eq_self_of_not_dvd` wants its last hypothesis in. -/
public theorem skip_not_dvd_live {lrecs llo lcnt lchunk live : Nat}
    {srecs slo scnt schunk skipProd i j d : Nat}
    (hlchunk : prodChunkK lrecs llo lcnt d 0 = lchunk) (hlive : lchunk ∣ live)
    (hschunk : prodChunkK srecs slo scnt d 0 = schunk) (hskip : schunk ∣ skipProd)
    (hgcd : Nat.gcd live skipProd = 1)
    (hne : valueK (Nat.add slo i) ≠ 1)
    (hi : Nat.testBit (asmChunkK srecs scnt d 0) i = true)
    (hj : Nat.testBit (asmChunkK lrecs lcnt d 0) j = true) :
    ¬ (valueK (Nat.add slo i) ∣ valueK (Nat.add llo j)) := by
  refine not_dvd_of_coprime_products hgcd ?_ (dvd_skipProd_of_testBit hschunk hskip hi) hne
  refine Nat.dvd_trans ?_ hlive
  rw [← hlchunk]
  exact dvd_prodChunkK_of_testBit lrecs llo lcnt d 0 j hj

/-- A bit of a checked union is a bit of one of its sides.

This is what lets a chunk's assembly be stated inside its cover step rather than beside it. From
`lor acc (asmChunkK …) = next`, a bit of `next` is a bit of `acc` or a bit of `asmChunkK …`, and
the second is already what `skip_not_dvd_live` asks for; the separate literal was a step on the
way to the same place. -/
public theorem testBit_of_lor_eq {a b c j : Nat} (h : Nat.lor a b = c)
    (hj : Nat.testBit c j = true) :
    Nat.testBit a j = true ∨ Nat.testBit b j = true := by
  rw [← h] at hj
  change Nat.testBit (a ||| b) j = true at hj
  rw [Nat.testBit_or] at hj
  cases h1 : Nat.testBit a j with
  | true => exact Or.inl rfl
  | false =>
    rw [h1, Bool.false_or] at hj
    exact Or.inr hj

/-! ## A slice's bits are the window's bits

The certificate is stated a slice at a time, because a record is sixteen bits wide and a slice is
what one can address. So a live bit of the window at `k * 65536 + j` has to be known to be the
slice's live bit at `j`, where the slice is the window shifted down and masked — which is what the
emitter states and the kernel checks. -/

/-- A bit of the window inside a slice is the matching bit of that slice. -/
public theorem testBit_slice {seg s w j : Nat} (hj : j < w)
    (h : Nat.testBit seg (s + j) = true) :
    Nat.testBit (Nat.land (Nat.shiftRight seg s) (Nat.sub (Nat.shiftLeft 1 w) 1)) j = true := by
  change Nat.testBit ((seg >>> s) &&& (1 <<< w - 1)) j = true
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_two_pow_sub_one]
  rw [h, decide_eq_true hj, Bool.and_true]

/-- And the other way: a bit of the slice is a bit of the window, which is the direction that
carries a gcd about the slice back to the window's live values. -/
public theorem testBit_of_testBit_slice {seg s w j : Nat}
    (h : Nat.testBit (Nat.land (Nat.shiftRight seg s) (Nat.sub (Nat.shiftLeft 1 w) 1)) j = true) :
    Nat.testBit seg (s + j) = true := by
  change Nat.testBit ((seg >>> s) &&& (1 <<< w - 1)) j = true at h
  rw [Nat.testBit_and, Nat.testBit_shiftRight] at h
  exact ((Bool.and_eq_true _ _).mp h).1

end PrimeCert.Sieve
