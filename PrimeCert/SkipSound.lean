/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import PrimeCert.SegmentedSieve
public import PrimeCert.NoPos

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

/-! ## From one divisor at a time to the whole skipped set

`segLoopK_eq_of_skip` wants the finished window to share no bit with `maskUnionK` over the skipped
set — all of them at once. What the certificate gives, and what `segMarkK_eq_self_of_not_dvd`
consumes, is one divisor at a time. This is the step between: `land` distributes over `lor`, so a
union of masks that each miss the window misses it too, and the fold peels one divisor a step.

With this the chain runs end to end. The certificate says no live value is a multiple of a skipped
divisor; `mask_iff` in `SieveCorrect` turns that into each skipped divisor's mask missing the
window; this turns the collection of those into the hypothesis the skip step takes; and
`segLoopK_eq_of_skip` gives back that marking with the subset is marking with everything. -/

/-- Disjointness survives a union: this is the whole of why the skipped divisors can be dropped
together rather than one at a time. -/
public theorem land_lor_eq_zero {a u m : Nat} (hu : Nat.land a u = 0) (hm : Nat.land a m = 0) :
    Nat.land a (Nat.lor u m) = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  -- `Nat.testBit_and` is stated with `&&&`, the hypotheses with `Nat.land`, so the notation has
  -- to be put back before the hypothesis will rewrite.
  have hu' : (Nat.testBit a i && Nat.testBit u i) = false := by
    rw [← Nat.testBit_and]
    change Nat.testBit (Nat.land a u) i = false
    rw [hu, Nat.zero_testBit]
  have hm' : (Nat.testBit a i && Nat.testBit m i) = false := by
    rw [← Nat.testBit_and]
    change Nat.testBit (Nat.land a m) i = false
    rw [hm, Nat.zero_testBit]
  change Nat.testBit (a &&& (u ||| m)) i = Nat.testBit 0 i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, Bool.and_or_distrib_left, hu', hm']
  rfl

/-- A union of masks that each share no bit with `seg` shares none either. The hypothesis is per
divisor and names only the ones the bitset actually holds, since the fold skips the rest. -/
public theorem land_maskUnionK_eq_zero {sS lo Wm1 seg start : Nat} : ∀ fuel : Nat,
    (∀ i, i < fuel → testBitK sS (start + i) = true →
      Nat.land seg (maskOfK (valueK (start + i)) lo Wm1) = 0) →
    Nat.land seg (maskUnionK sS lo Wm1 start fuel) = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro _
    have h0 : maskUnionK sS lo Wm1 start 0 = 0 := rfl
    rw [h0]
    change seg &&& 0 = 0
    exact Nat.and_zero seg
  | succ k ih =>
    intro h
    rw [maskUnionK_succ]
    cases hb : testBitK sS (start + k) with
    | false =>
      dsimp only
      exact ih fun i hi hs => h i (Nat.lt_succ_of_lt hi) hs
    | true =>
      dsimp only
      refine land_lor_eq_zero (ih fun i hi hs => h i (Nat.lt_succ_of_lt hi) hs) ?_
      exact h k (Nat.lt_succ_self k) hb

/-! ## The certificate, composed

`segLoopK_eq_self_of_blocks` is this statement for the shape the record certificate replaced: a
whole range of divisors leaves the window alone, given one gcd a block and that each divisor
divides `P`. Its gcd hypothesis is over `prodLiveFromK`, which walks the window a bit at a time
and is what ran to 40 GB. The two theorems below are its twin over records.

The cover is stated existentially — every live position is held by *some* chunk — rather than by
indexing the chunks. Indexing would put the emitter's layout into the statement, and the layout is
a tuning knob; the existential is also exactly what the emitted statements discharge, a slice at a
time. Only one offset is free, the slice's base `b`: a chunk's assembly is read at `j - b` and its
product taken from `lo + b`, and `valueK (lo + j)` is then the same number as
`valueK ((lo + b) + (j - b))`. -/

/-- Every live position names a value no divisor of `P` divides, given each live position is held
by some chunk whose product is coprime to `P`. This is the hypothesis
`segMarkK_eq_self_of_not_dvd` takes, assembled from what the certificate states. -/
public theorem not_dvd_of_cover {seg lo P p : Nat} (hp : p ∣ P) (hp1 : p ≠ 1)
    (hcov : ∀ j, Nat.testBit seg j = true →
      ∃ recs cnt d b, b ≤ j ∧ Nat.testBit (asmChunkK recs cnt d 0) (j - b) = true ∧
        Nat.gcd (prodChunkK recs (Nat.add lo b) cnt d 0) P = 1) :
    ∀ j, Nat.testBit seg j = true → ¬ (p ∣ valueK (Nat.add lo j)) := by
  intro j hj
  obtain ⟨recs, cnt, d, b, hb, hasm, hgcd⟩ := hcov j hj
  have hsplit : Nat.add lo j = Nat.add (Nat.add lo b) (j - b) := by
    change lo + j = lo + b + (j - b)
    omega
  rw [hsplit]
  refine not_dvd_of_coprime_products hgcd ?_ hp hp1
  exact dvd_prodChunkK_of_testBit recs (Nat.add lo b) cnt d 0 (j - b) hasm

/-- **The record certificate.** A whole range of divisors leaves the window alone, given that each
divides `P` and that every live position of the window is held by a chunk whose product is coprime
to `P`.

The same induction as `segLoopK_eq_self_of_blocks`, with the middle hypothesis coming from the
cover rather than from a product over the window's bits. -/
public theorem segLoopK_eq_self_of_records {s lo Wm1 seg start fuel P : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 2 ^ 32)
    (hcov : ∀ j, Nat.testBit seg j = true →
      ∃ recs cnt d b, b ≤ j ∧ Nat.testBit (asmChunkK recs cnt d 0) (j - b) = true ∧
        Nat.gcd (prodChunkK recs (Nat.add lo b) cnt d 0) P = 1)
    (hdiv : ∀ i, i < fuel → testBitK s (start + i) = true →
      (valueK (start + i) % 6 = 1 ∨ valueK (start + i) % 6 = 5) ∧ 5 ≤ valueK (start + i) ∧
        index (valueK (start + i) * 7) ≤ lo ∧ valueK (start + i) ∣ P) :
    segLoopK s lo Wm1 seg start fuel = seg := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hrec : segLoopK s lo Wm1 seg start fuel = seg :=
      ih fun i hi => hdiv i (by omega)
    rw [segLoopK_succ, hrec]
    cases hb : testBitK s (start + fuel) with
    | false => rfl
    | true =>
      obtain ⟨h6, h5, hlo, hP⟩ := hdiv fuel (by omega) hb
      refine segMarkK_eq_self_of_not_dvd hseg hW h6 h5 hlo fun j _ hlive => ?_
      -- `testBitK` is `Nat.testBit`, which is what the cover is stated with.
      rw [Sieve.testBitK_eq_testBit] at hlive
      exact not_dvd_of_cover hP (by omega) hcov j hlive

/-- **The record certificate over several products.** The same statement as
`segLoopK_eq_self_of_records`, with the single product replaced by a list of them: each skipped
divisor divides one of the products, and every live position is held by a chunk coprime to each.

The single-product form builds one literal from every skipped divisor, 5519007 of them at `10^16`
and 16797927 at `10^17`, by multiplying the chunk products pairwise up a tree. A list lets the
emitter stop at any level of that tree and state the gcds against the pieces, which is the
staging that segmented work allows and that the one-literal form forbids.

The proof is the single-product proof. The induction never looks at more than one divisor, so it
only ever needs the product that divisor divides, and the cover stated against that product. -/
public theorem segLoopK_eq_self_of_records_list {s lo Wm1 seg start fuel : Nat} {Ps : List Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 2 ^ 32)
    (hcov : ∀ P ∈ Ps, ∀ j, Nat.testBit seg j = true →
      ∃ recs cnt d b, b ≤ j ∧ Nat.testBit (asmChunkK recs cnt d 0) (j - b) = true ∧
        Nat.gcd (prodChunkK recs (Nat.add lo b) cnt d 0) P = 1)
    (hdiv : ∀ i, i < fuel → testBitK s (start + i) = true →
      (valueK (start + i) % 6 = 1 ∨ valueK (start + i) % 6 = 5) ∧ 5 ≤ valueK (start + i) ∧
        index (valueK (start + i) * 7) ≤ lo ∧ ∃ P ∈ Ps, valueK (start + i) ∣ P) :
    segLoopK s lo Wm1 seg start fuel = seg := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hrec : segLoopK s lo Wm1 seg start fuel = seg :=
      ih fun i hi => hdiv i (by omega)
    rw [segLoopK_succ, hrec]
    cases hb : testBitK s (start + fuel) with
    | false => rfl
    | true =>
      obtain ⟨h6, h5, hlo, P, hmem, hP⟩ := hdiv fuel (by omega) hb
      refine segMarkK_eq_self_of_not_dvd hseg hW h6 h5 hlo fun j _ hlive => ?_
      rw [Sieve.testBitK_eq_testBit] at hlive
      exact not_dvd_of_cover hP (by omega) (hcov P hmem) j hlive

/-! ## The join

This is the theorem the whole design exists to produce, and the one the emitter stubbed while its
cost was being measured: marking by **every** divisor gives the window the route built from the
subset. Everything above is a piece of it.

The chain has no induction of its own. Marking is a set difference against the union of the
masks, so:

  marking by `s`                       is `seg` minus the union over `s`
                                       (`segLoopK_eq_ldiff_union`)
  the union over `sMark ||| sSkip`     splits (`maskUnionK_or`, and the split identity the
                                       emitter checks says that bitset is `s`)
  two differences collapse into one    (`ldiff_ldiff`), so this is marking by `sMark` and then
                                       by `sSkip`
  marking by `sMark` is the window     (the route's own theorem)
  marking the window by `sSkip`        changes nothing (`segLoopK_eq_self_of_records`, from the
                                       certificate)

and the last two leave the window. -/

/-- **The design's theorem.** Given the emitter's split identity, the route's theorem about the
marked subset, and the certificate's two facts about the window and the skipped divisors, marking
by every divisor gives the same window.

`hcov` is the cover: every live position of the window is held by a chunk whose product is coprime
to `P`. `hdiv` is the skipped side: every divisor the sweep left out divides `P`, and is a number
the sieve could have marked with. -/
public theorem segLoopK_eq_of_certificate {sVal sMark sSkip lo Wm1 seg win fuel P : Nat}
    (hsplit : Nat.lor sMark sSkip = sVal)
    (hroute : segLoopK sMark lo Wm1 seg 1 fuel = win)
    (hwin : win < 2 ^ (Wm1 + 1)) (hW : Wm1 < 2 ^ 32)
    (hcov : ∀ j, Nat.testBit win j = true →
      ∃ recs cnt d b, b ≤ j ∧ Nat.testBit (asmChunkK recs cnt d 0) (j - b) = true ∧
        Nat.gcd (prodChunkK recs (Nat.add lo b) cnt d 0) P = 1)
    (hdiv : ∀ i, i < fuel → testBitK sSkip (1 + i) = true →
      (valueK (1 + i) % 6 = 1 ∨ valueK (1 + i) % 6 = 5) ∧ 5 ≤ valueK (1 + i) ∧
        index (valueK (1 + i) * 7) ≤ lo ∧ valueK (1 + i) ∣ P) :
    segLoopK sVal lo Wm1 seg 1 fuel = win := by
  -- Marking the finished window by the skipped divisors changes nothing. This is the
  -- certificate's whole content, and it is where `P` and the cover are used.
  have hskip : segLoopK sSkip lo Wm1 win 1 fuel = win :=
    segLoopK_eq_self_of_records hwin hW hcov hdiv
  -- The rest is bookkeeping about set differences, with no induction. Written as a chain of
  -- named steps rather than one `rw`: several of these rewrites match in more than one place,
  -- and which one fires first is not something to leave to chance in a file I cannot compile.
  have hsplitU : maskUnionK sVal lo Wm1 1 fuel
      = Nat.lor (maskUnionK sMark lo Wm1 1 fuel) (maskUnionK sSkip lo Wm1 1 fuel) := by
    rw [← hsplit]
    exact maskUnionK_or
  have hmark : Nat.ldiff seg (maskUnionK sMark lo Wm1 1 fuel) = win := by
    rw [← segLoopK_eq_ldiff_union]
    exact hroute
  calc segLoopK sVal lo Wm1 seg 1 fuel
      = Nat.ldiff seg (maskUnionK sVal lo Wm1 1 fuel) := segLoopK_eq_ldiff_union
    _ = Nat.ldiff seg (Nat.lor (maskUnionK sMark lo Wm1 1 fuel)
          (maskUnionK sSkip lo Wm1 1 fuel)) := by rw [hsplitU]
    _ = Nat.ldiff (Nat.ldiff seg (maskUnionK sMark lo Wm1 1 fuel))
          (maskUnionK sSkip lo Wm1 1 fuel) := ldiff_ldiff.symm
    _ = Nat.ldiff win (maskUnionK sSkip lo Wm1 1 fuel) := by rw [hmark]
    _ = segLoopK sSkip lo Wm1 win 1 fuel := segLoopK_eq_ldiff_union.symm
    _ = win := hskip

/-! ## Positions to slices, which is the step chunks cannot do

Worth recording, because it is the thing that shapes everything above.
`segMarkK_eq_self_of_not_dvd` wants a fact about every live position, and the certificate supplies
facts about chunks. `not_dvd_of_blocks` does the same crossing for the older shape, and it works
because blocks are a uniform partition of positions: the block holding `j` is `j / bs`.

Chunks are not uniform. A chunk is a fixed number of *records*, and records are the live
positions, which are irregular, so no arithmetic names the chunk holding `j`, and a hypothesis
quantified over every live `j` has nothing to compute with.

Slices are uniform, so the arithmetic works on them, and that is how `dvd_of_sliceCov` crosses: it
carries the cover along the emitted chain and uses `j / 65536` to find the slice. An earlier
`not_dvd_of_slices` here took the per-slice fact as a hypothesis instead and left the caller to
produce it; `dvd_of_sliceCov` subsumes it, so it is gone. -/

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

/-! ## The join, as the emitter proves it

The emitter states every fact below as a `Nat.beq` the kernel evaluates, and these lemmas are the
steps of the term it builds from them. One predicate carries the whole argument: `BitsDvd x L D`,
every set bit of `x` names a value, read from `L`, that divides `D`.

A chunk has it from its assembly and its product (`bitsDvd_chunk`), the cover chain passes it
along each `lor` (`bitsDvd_lor`), the slice statement moves it onto the window's slice
(`bitsDvd_of_beq`), and `SliceCov` collects the slices. The chunk product dividing `D` comes from
the multiplication tree, a factor at a time (`dvd_of_mul_beq_left`, `dvd_of_mul_beq_right`). On the
live side `D` is the live product, coprime to `P` by the one gcd; on the skipped side `D` is `P`. -/

/-- Every set bit of `x` names a value, read from `L`, that divides `D`. -/
@[expose] public def BitsDvd (x L D : Nat) : Prop :=
  ∀ j, Nat.testBit x j = true → valueK (Nat.add L j) ∣ D

public theorem bitsDvd_zero {L D : Nat} : BitsDvd 0 L D := by
  intro j hj
  rw [Nat.zero_testBit] at hj
  exact absurd hj (by decide)

public theorem bitsDvd_of_beq {x y L D : Nat} (h : Nat.beq x y = true) (hy : BitsDvd y L D) :
    BitsDvd x L D := by
  rw [Nat.eq_of_beq_eq_true h]
  exact hy

/-- One step of a cover chain. -/
public theorem bitsDvd_lor {acc asm next L D : Nat} (hacc : BitsDvd acc L D)
    (hasm : BitsDvd asm L D) (h : Nat.beq (Nat.lor acc asm) next = true) : BitsDvd next L D := by
  intro j hj
  rcases testBit_of_lor_eq (Nat.eq_of_beq_eq_true h) hj with h1 | h1
  · exact hacc j h1
  · exact hasm j h1

/-- A chunk's assembled bits name values dividing anything its product divides.

`off` is a variable so that the emitter passes the literal its statements carry, which makes each
hypothesis syntactically the statement it is given and spares the kernel re-evaluating the chunk. -/
public theorem bitsDvd_chunk {recs L cnt d off asm pv D : Nat}
    (hasm : Nat.beq (asmChunkK recs cnt d off) asm = true)
    (hprod : Nat.beq (prodChunkK recs L cnt d off) pv = true) (hdvd : pv ∣ D) :
    BitsDvd asm L D := by
  intro j hj
  rw [← Nat.eq_of_beq_eq_true hasm] at hj
  refine Nat.dvd_trans ?_ hdvd
  rw [← Nat.eq_of_beq_eq_true hprod]
  exact dvd_prodChunkK_of_testBit recs L cnt d off j hj

/-- `bitsDvd_chunk` for a chunk whose product is stated as `prodQuadK`, four records a leaf.

The offsets are variables for the reason `bitsDvd_chunk`'s is: the emitter passes the literals its
statements carry, so each hypothesis is syntactically the statement it is given. -/
public theorem bitsDvd_chunkQ {recs L cnt d e aoff qoff asm pv D : Nat}
    (hasm : Nat.beq (asmChunkK recs cnt d aoff) asm = true)
    (hprod : Nat.beq (prodQuadK recs L e qoff) pv = true) (hdvd : pv ∣ D)
    (hoff : Nat.beq aoff (4 * qoff) = true)
    (hde : Nat.ble (aoff + 2 ^ d) (4 * (qoff + 2 ^ e)) = true) :
    BitsDvd asm L D := by
  intro j hj
  rw [← Nat.eq_of_beq_eq_true hasm] at hj
  refine Nat.dvd_trans ?_ hdvd
  rw [← Nat.eq_of_beq_eq_true hprod]
  exact dvd_prodQuadK_of_testBit hoff hde hj

/-- `bitsDvd_chunkQ` for a chunk whose assembly is stated as `asmQuadK` as well, four records a
leaf on both sides.

`asmQuadK_eq_asmChunkK` carries the wide assembly to the narrow one two levels deeper, so this
needs no argument of its own beyond the condition that lets it: every slot the wide tree reads is
below `cnt`, which the emitter arranges by padding a part-full chunk with copies of its last
record. -/
public theorem bitsDvd_chunkQA {recs L cnt a e off qoff asm pv D : Nat}
    (hasm : Nat.beq (asmQuadK recs a off) asm = true)
    (hprod : Nat.beq (prodQuadK recs L e qoff) pv = true) (hdvd : pv ∣ D)
    (hcnt : Nat.ble (4 * (off + 2 ^ a)) cnt = true)
    (hoff : Nat.beq off qoff = true)
    (hde : Nat.ble (2 ^ (a + 2)) (4 * 2 ^ e) = true) :
    BitsDvd asm L D := by
  have ho := Nat.eq_of_beq_eq_true hoff
  subst ho
  have hwide := asmQuadK_eq_asmChunkK recs cnt a off (Nat.le_of_ble_eq_true hcnt)
  rw [hwide] at hasm
  have hle := Nat.le_of_ble_eq_true hde
  refine bitsDvd_chunkQ (cnt := cnt) (d := a + 2) (aoff := 4 * off) hasm hprod hdvd ?_ ?_
  · exact Nat.beq_refl _
  · exact Nat.ble_eq.mpr (by omega)

/-- `bitsDvd_chunk` for a chunk whose product is stated as `prodOctK`, eight records a leaf. The
same statement `bitsDvd_chunkQ` makes for four. -/
public theorem bitsDvd_chunkO {recs L cnt d e aoff qoff asm pv D : Nat}
    (hasm : Nat.beq (asmChunkK recs cnt d aoff) asm = true)
    (hprod : Nat.beq (prodOctK recs L e qoff) pv = true) (hdvd : pv ∣ D)
    (hoff : Nat.beq aoff (8 * qoff) = true)
    (hde : Nat.ble (aoff + 2 ^ d) (8 * (qoff + 2 ^ e)) = true) :
    BitsDvd asm L D := by
  intro j hj
  rw [← Nat.eq_of_beq_eq_true hasm] at hj
  refine Nat.dvd_trans ?_ hdvd
  rw [← Nat.eq_of_beq_eq_true hprod]
  exact dvd_prodOctK_of_testBit hoff hde hj

/-- `bitsDvd_chunkO` for a chunk whose assembly is stated as `asmOctK` as well, eight records a
leaf on both sides. `asmOctK_eq_asmChunkK` carries the wide assembly to the narrow one three
levels deeper, on the same condition `bitsDvd_chunkQA` needs two levels deeper: every slot the
wide tree reads is below `cnt`, which the emitter arranges by padding a part-full chunk with
copies of its last record. -/
public theorem bitsDvd_chunkOA {recs L cnt a e off qoff asm pv D : Nat}
    (hasm : Nat.beq (asmOctK recs a off) asm = true)
    (hprod : Nat.beq (prodOctK recs L e qoff) pv = true) (hdvd : pv ∣ D)
    (hcnt : Nat.ble (8 * (off + 2 ^ a)) cnt = true)
    (hoff : Nat.beq off qoff = true)
    (hde : Nat.ble (2 ^ (a + 3)) (8 * 2 ^ e) = true) :
    BitsDvd asm L D := by
  have ho := Nat.eq_of_beq_eq_true hoff
  subst ho
  have hwide := asmOctK_eq_asmChunkK recs cnt a off (Nat.le_of_ble_eq_true hcnt)
  rw [hwide] at hasm
  have hle := Nat.le_of_ble_eq_true hde
  refine bitsDvd_chunkO (cnt := cnt) (d := a + 3) (aoff := 8 * off) hasm hprod hdvd ?_ ?_
  · exact Nat.beq_refl _
  · exact Nat.ble_eq.mpr (by omega)

public theorem dvd_of_mul_beq_left {a b c D : Nat} (h : Nat.beq (Nat.mul a b) c = true)
    (hc : c ∣ D) : a ∣ D :=
  Nat.dvd_trans (dvd_of_mul_eq (Nat.eq_of_beq_eq_true h)).1 hc

public theorem dvd_of_mul_beq_right {a b c D : Nat} (h : Nat.beq (Nat.mul a b) c = true)
    (hc : c ∣ D) : b ∣ D :=
  Nat.dvd_trans (dvd_of_mul_eq (Nat.eq_of_beq_eq_true h)).2 hc

/-- `BitsDvd` for each of the first `n` slices of 65536 bits of `x`, slice `k` read from
`L + k * 65536`. -/
@[expose] public def SliceCov (x L D n : Nat) : Prop :=
  ∀ k, k < n → BitsDvd (Nat.land (Nat.shiftRight x (Nat.mul k 65536))
    (Nat.sub (Nat.shiftLeft 1 65536) 1)) (Nat.add L (Nat.mul k 65536)) D

public theorem sliceCov_zero {x L D : Nat} : SliceCov x L D 0 :=
  fun _ hk => absurd hk (Nat.not_lt_zero _)

public theorem sliceCov_succ {x L D n : Nat} (h : SliceCov x L D n)
    (hn : BitsDvd (Nat.land (Nat.shiftRight x (Nat.mul n 65536))
      (Nat.sub (Nat.shiftLeft 1 65536) 1)) (Nat.add L (Nat.mul n 65536)) D) :
    SliceCov x L D (n + 1) := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
  · exact h k hlt
  · rw [heq]
    exact hn

/-- `sliceCov_succ` with the slice's shift `o`, mask `m`, base `Lk` and the next count `n'` as
variables, so the emitter passes the literals its slice statements carry and each hypothesis is
syntactically the statement it is given. -/
public theorem sliceCov_step {x L D n n' o m Lk : Nat} (h : SliceCov x L D n)
    (ho : Nat.beq o (Nat.mul n 65536) = true)
    (hm : Nat.beq m (Nat.sub (Nat.shiftLeft 1 65536) 1) = true)
    (hL : Nat.beq Lk (Nat.add L o) = true) (hn' : Nat.beq n' (n + 1) = true)
    (hn : BitsDvd (Nat.land (Nat.shiftRight x o) m) Lk D) : SliceCov x L D n' := by
  have e1 := Nat.eq_of_beq_eq_true ho
  have e2 := Nat.eq_of_beq_eq_true hm
  have e3 := Nat.eq_of_beq_eq_true hL
  have e4 := Nat.eq_of_beq_eq_true hn'
  subst e1 e2 e3 e4
  exact sliceCov_succ h hn

/-- The slices give every set bit of `x` below `n * 65536`. -/
public theorem dvd_of_sliceCov {x L D n m : Nat} (h : SliceCov x L D n) (hm : m < n * 65536)
    (hb : Nat.testBit x m = true) : valueK (Nat.add L m) ∣ D := by
  have hk : m / 65536 < n := by omega
  have hr : m % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have hsplit : Nat.mul (m / 65536) 65536 + m % 65536 = m := by
    change m / 65536 * 65536 + m % 65536 = m
    omega
  have hb' : Nat.testBit x (Nat.mul (m / 65536) 65536 + m % 65536) = true := by
    rw [hsplit]
    exact hb
  have key : valueK (Nat.add (Nat.add L (Nat.mul (m / 65536) 65536)) (m % 65536)) ∣ D :=
    h (m / 65536) hk (m % 65536) (testBit_slice hr hb')
  have he : Nat.add (Nat.add L (Nat.mul (m / 65536) 65536)) (m % 65536) = Nat.add L m := by
    change L + m / 65536 * 65536 + m % 65536 = L + m
    omega
  rw [he] at key
  exact key

public theorem testBit_asmChunkK_single : Nat.testBit (asmChunkK 0 1 0 0) 0 = true := by
  decide +kernel

public theorem prodChunkK_single (L : Nat) : prodChunkK 0 L 1 0 0 = valueK L := by
  have h0 : Nat.land (Nat.shiftRight 0 (Nat.mul 0 16)) 65535 = 0 := by decide +kernel
  have hb : Nat.blt 0 1 = true := by decide +kernel
  have hp : prodChunkK 0 L 1 0 0 = (Nat.blt 0 1).rec 1
      (valueK (Nat.add L (Nat.land (Nat.shiftRight 0 (Nat.mul 0 16)) 65535))) := rfl
  rw [hp, hb, h0]
  all_goals rfl

/-- **The emitted window theorem.** Marking by every divisor gives the window the route built from
the marked subset, from the facts the emitter states: the split identity, the route's theorem, the
live side's slices into `D` with `D` coprime to `P`, and the skipped side's slices into `P`.

The cover `segLoopK_eq_of_certificate` asks for is met by the single record naming `j` itself,
whose product is `valueK (lo + j)`, which divides `D`. -/
public theorem segLoopK_eq_of_join {sVal sMark sSkip lo Wm1 W win fuel P D nL nS : Nat}
    (hsplit : Nat.beq (Nat.lor sMark sSkip) sVal = true)
    (hroute : segLoopK sMark lo Wm1 (initSegK W) 1 fuel = win)
    (hW1 : Nat.beq (Wm1 + 1) W = true) (hW : Nat.blt Wm1 (2 ^ 32) = true)
    (hnL : Nat.ble W (nL * 65536) = true) (hlive : SliceCov win lo D nL)
    (hgcd : Nat.beq (Nat.gcd D P) 1 = true)
    (hnS : Nat.blt fuel (nS * 65536) = true) (hskip : SliceCov sSkip 0 P nS)
    (hlo : Nat.ble (index (valueK fuel * 7)) lo = true) :
    segLoopK sVal lo Wm1 (initSegK W) 1 fuel = win := by
  have hw : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hW1
  have hWlt : Wm1 < 2 ^ 32 := Nat.blt_eq.mp hW
  have hwin' : win < 2 ^ W := by
    rw [← hroute]
    exact Nat.lt_of_le_of_lt segLoopK_le initSegK_lt
  have hwin : win < 2 ^ (Wm1 + 1) := by
    rw [hw]
    exact hwin'
  have hWn : W ≤ nL * 65536 := Nat.le_of_ble_eq_true hnL
  have hD : ∀ j, Nat.testBit win j = true → valueK (Nat.add lo j) ∣ D := by
    intro j hj
    refine dvd_of_sliceCov hlive ?_ hj
    by_cases hc : j < nL * 65536
    · exact hc
    · exfalso
      have hle : W ≤ j := by omega
      have hlt : win < 2 ^ j :=
        Nat.lt_of_lt_of_le hwin' (Nat.pow_le_pow_right (by decide) hle)
      rw [Nat.testBit_eq_false_of_lt hlt] at hj
      exact absurd hj (by decide)
  have hcov : ∀ j, Nat.testBit win j = true →
      ∃ recs cnt d b, b ≤ j ∧ Nat.testBit (asmChunkK recs cnt d 0) (j - b) = true ∧
        Nat.gcd (prodChunkK recs (Nat.add lo b) cnt d 0) P = 1 := by
    intro j hj
    refine ⟨0, 1, 0, j, Nat.le_refl j, ?_, ?_⟩
    · rw [Nat.sub_self]
      exact testBit_asmChunkK_single
    · rw [prodChunkK_single]
      exact Nat.Coprime.coprime_dvd_left (hD j hj) (Nat.eq_of_beq_eq_true hgcd)
  have hfuel : fuel < nS * 65536 := Nat.blt_eq.mp hnS
  have hdiv : ∀ i, i < fuel → testBitK sSkip (1 + i) = true →
      (valueK (1 + i) % 6 = 1 ∨ valueK (1 + i) % 6 = 5) ∧ 5 ≤ valueK (1 + i) ∧
        index (valueK (1 + i) * 7) ≤ lo ∧ valueK (1 + i) ∣ P := by
    intro i hi hb
    rw [testBitK_eq_testBit] at hb
    have hd : valueK (Nat.add 0 (1 + i)) ∣ P := dvd_of_sliceCov hskip (by omega) hb
    have he : Nat.add 0 (1 + i) = 1 + i := Nat.zero_add _
    rw [he] at hd
    have hv : valueK (1 + i) * 7 ≤ valueK fuel * 7 := by
      have := valueK_le (i := 1 + i) (j := fuel) (by omega)
      omega
    refine ⟨valueK_mod6 _, five_le_valueK (by omega), ?_, hd⟩
    exact Nat.le_trans (index_mono hv) (Nat.le_of_ble_eq_true hlo)
  exact segLoopK_eq_of_certificate (Nat.eq_of_beq_eq_true hsplit) hroute hwin hWlt hcov hdiv

/-! ## The divisors with no position in the window

`hdiv` above asks every skipped divisor to divide the product `P`, so the skipped side carries one
factor per skipped divisor: 5519007 at `10^16` and 50519424 at `10^18`. Most of those divisors are
skipped for a reason that never reaches the window's live positions, having no multiple at a
window position at all, which is 4688449 of the 5519007 and 49281838 of the 50519424.

`PrimeCert.NoPos` states that reason as one fold per batch and takes it back apart. This is the
last step: a divisor the fold names leaves the window exactly as it was, with no product and no
gcd anywhere in the argument. -/

/-- A divisor named by a true batch fold leaves the window exactly as it was.

`NoPos.firstOffK` and `firstLocK` have the same body, so the mask in `segMarkK` is the mask
`land_mask_eq_zero_of_noPosFoldK` speaks about and the two statements meet without conversion. -/
public theorem segMarkK_eq_self_of_noPosFoldK {c lo Wm1 start fuel i seg : Nat}
    (hfold : noPosFoldK c lo Wm1 start fuel = true) (hi : i < fuel)
    (hbit : Nat.blt 0 (Nat.land c (Nat.shiftLeft 1 i)) = true)
    (hseg : ∀ j, Wm1 < j → Nat.testBit seg j = false) :
    segMarkK seg (valueK (Nat.add start i)) lo Wm1 = seg := by
  have hz : Nat.land seg (buildMaskK (valueK (Nat.add start i)) Wm1
      (firstLocK (indexK ((valueK (Nat.add start i)).mul 5)) lo ((valueK (Nat.add start i)).mul 2))
      (firstLocK (indexK ((valueK (Nat.add start i)).mul 7)) lo ((valueK (Nat.add start i)).mul 2))
      32) = 0 := land_mask_eq_zero_of_noPosFoldK hfold hi hbit hseg
  change Nat.sub seg (Nat.land seg _) = seg
  rw [hz]
  exact Nat.sub_zero seg

end PrimeCert.Sieve
