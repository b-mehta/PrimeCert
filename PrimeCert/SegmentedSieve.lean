/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public meta import SieveEmit
public import PrimeCert.Sieve
public import PrimeCert.SieveCorrect
public import PrimeCert.SieveBase
public import PrimeCert.ForMathlibBitwise
public import Mathlib.Data.Nat.Bitwise

/-!
# A segmented sieve prototype

A window of `W` consecutive mod-6 wheel positions, starting at the wheel index `lo = index a`, is
held in one natural number `seg` used as a `W`-bit bitset: bit `j` of `seg` stands for the number
`value (lo + j)`. `segLoopK` walks the base sieve `s` and, at each index whose bit is set, clears
that prime's multiples from the window.

The translation from the global index space to the window is entirely in the *seeds* of the mask:
the multiples of `p` sit at the global indices `index (5*p) + 2*p*j` and `index (7*p) + 2*p*j`, so
in the window they sit at the local offsets congruent to those seeds modulo `2*p`, and
`firstLocK` computes the smallest such offset. `buildMaskK` from `PrimeCert.Sieve` is then reused
verbatim to grow each seed into a stride-`2*p` mask across the window.

This is a prototype. The kernel-checked statement is the fold equation
`segLoopK s lo Wm1 (initSegK W) 1 fuel = <literal>`; `segmentSound_of` bridges from that to the
absence of small prime factors. See the module note at `SegmentSound`.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Kernel-side definitions -/

/-- A window of `W` live candidates: the low `W` bits set, i.e. `2^W - 1`. -/
@[expose] public def initSegK (W : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 W) 1

/-- The least offset `j` with `lo + j` in the residue class of `A` modulo `m`. Written against
`lo % m` rather than `lo / m`, so that neither the quotient nor the product `m * (lo / m)` is
formed. -/
@[expose] public def firstLocK (A lo m : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add A m) (Nat.mod lo m)) m

/-- Clear from the window `seg` every local offset holding a coprime-to-6 multiple of `p`. -/
@[expose] public noncomputable def segMarkK (seg p lo Wm1 : Nat) : Nat :=
  seg.sub (seg.land
    (buildMaskK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
      (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 32))

/-- Sieve the window `seg` by the base primes recorded in the bitset `s`, scanning the base
indices `start, start+1, …` for `fuel` steps. -/
@[expose] public noncomputable def segLoopK (s lo Wm1 seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK s (start.add i)).rec b (segMarkK b (valueK (start.add i)) lo Wm1)

/-! ## The fuel chain -/

/-- Loop recurrence: peel the top index `start+fuel`, in the exact `Bool.rec` form the def uses. -/
public theorem segLoopK_succ {s lo Wm1 seg start fuel : Nat} :
    segLoopK s lo Wm1 seg start (fuel + 1)
      = Bool.rec (segLoopK s lo Wm1 seg start fuel)
          (segMarkK (segLoopK s lo Wm1 seg start fuel) (valueK (start + fuel)) lo Wm1)
          (testBitK s (start + fuel)) := rfl

/-- Fuel additivity: running `a + b` steps is running `a` steps, then `b` more. -/
public theorem segLoopK_add {s lo Wm1 seg start a b : Nat} :
    segLoopK s lo Wm1 seg start (a + b)
      = segLoopK s lo Wm1 (segLoopK s lo Wm1 seg start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [segLoopK_succ]

/-- One chain step: a kernel-checked batch equation moves the run forward by `len` steps. -/
public theorem segLoopK_chain {L s lo Wm1 b b' start len rest : Nat}
    (hP : L = segLoopK s lo Wm1 b start (len.add rest))
    (h : (segLoopK s lo Wm1 b start len).beq b') :
    L = segLoopK s lo Wm1 b' (start.add len) rest := by
  grind [segLoopK_add, Nat.beq_eq]

/-- Last chain step: with no steps left, the batch equation gives the value of the whole run. -/
public theorem segLoopK_last {L s lo Wm1 b b' start len : Nat}
    (hP : L = segLoopK s lo Wm1 b start len)
    (h : (segLoopK s lo Wm1 b start len).beq b') :
    L = b' := by
  grind [Nat.beq_eq]

/-! ## Draft variants, for timing

Two changes to the loop above, kept beside it so that `run_segment_variant` can time them against
it. Each computes the same window as `segLoopK` on every window `seg < 2 ^ (Wm1 + 1)`; that
agreement is checked per batch against the same compiled twin, and is not proved here. -/

/-- `2 ^ A` when `A ≤ M`, and `0` otherwise: a seed bit, dropped when it lies above the window. -/
@[expose] public noncomputable def seedK (A M : Nat) : Nat :=
  (Nat.ble A M).rec 0 (Nat.shiftLeft 1 A)

/-- `seg` with the bits of `hit` cleared, where `hit` is a subset of `seg`; `seg` itself when
`hit = 0`. -/
@[expose] public noncomputable def clearHitK (seg hit : Nat) : Nat :=
  (Nat.ble 1 hit).rec seg (seg.sub hit)

/-- `buildMaskK` with both seeds passed through `seedK`. -/
@[expose] public noncomputable def buildMaskCK (p M A B n : Nat) : Nat :=
  Nat.rec
    ((seedK A M).lor (seedK B M))
    (fun i Mk =>
      ((p.shiftLeft i.succ).ble M).rec Mk
        (Mk.lor (Mk.shiftLeft (p.shiftLeft i.succ))))
    n

/-- `buildMaskCK` with each doubling round done as a multiplication: joining a mask to itself
shifted by `sh` is multiplying it by `2 ^ sh + 1` whenever all the mask's bits lie below `sh`,
which the rounds maintain, since round `i` shifts by `p * 2 ^ (i + 1)` and the mask reaching it
spans that much. -/
@[expose] public noncomputable def buildMaskMK (p M A B n : Nat) : Nat :=
  Nat.rec
    ((seedK A M).lor (seedK B M))
    (fun i Mk =>
      ((p.shiftLeft i.succ).ble M).rec Mk
        (Mk.mul (Nat.succ (Nat.shiftLeft 1 (p.shiftLeft i.succ)))))
    n

/-- The masks of a batch's divisors joined, each built by doubling as `segMarkCK` builds them.
Emitted beside a batch to price mask construction; it settles no window. -/
@[expose] public noncomputable def orMaskCK (c lo Wm1 n start len : Nat) : Nat :=
  len.rec 0 fun i a =>
    (testBitK c i).rec a
      (a.lor (buildMaskCK (valueK (start.add i)) Wm1
        (firstLocK (indexK ((valueK (start.add i)).mul 5)) lo ((valueK (start.add i)).mul 2))
        (firstLocK (indexK ((valueK (start.add i)).mul 7)) lo ((valueK (start.add i)).mul 2)) n))

/-- Two consecutive windows' masks for each divisor of a batch, each built by doubling, joined and
clamped to the window's width. Emitted beside a batch to price mask construction across windows;
it settles no window. -/
@[expose] public noncomputable def orMask2CK (c lo Wm1 n start len W : Nat) : Nat :=
  len.rec 0 fun i a =>
    (testBitK c i).rec a
      (let p : Nat := valueK (start.add i)
       let d : Nat := p.mul 2
       a.lor (((buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo d)
                  (firstLocK (indexK (p.mul 7)) lo d) n).lor
               (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) (lo.add W) d)
                  (firstLocK (indexK (p.mul 7)) (lo.add W) d) n)).land
              (Nat.sub (Nat.shiftLeft 1 W) 1)))

/-- The same two windows, the second taken from the first by a shift. A divisor's pattern repeats
every `2 * p` positions, so the window `W` positions along carries the same mask moved back by
`W % (2 * p)`, provided the first is built one period wider. -/
@[expose] public noncomputable def orMask2SK (c lo Wm1 n start len W : Nat) : Nat :=
  len.rec 0 fun i a =>
    (testBitK c i).rec a
      (let p : Nat := valueK (start.add i)
       let d : Nat := p.mul 2
       let base : Nat := buildMaskCK p (Wm1.add d) (firstLocK (indexK (p.mul 5)) lo d)
         (firstLocK (indexK (p.mul 7)) lo d) n
       a.lor ((base.lor (base.shiftRight (Nat.mod W d))).land
              (Nat.sub (Nat.shiftLeft 1 W) 1)))

/-- `orMaskCK` with the masks built by multiplication. -/
@[expose] public noncomputable def orMaskMK (c lo Wm1 n start len : Nat) : Nat :=
  len.rec 0 fun i a =>
    (testBitK c i).rec a
      (a.lor (buildMaskMK (valueK (start.add i)) Wm1
        (firstLocK (indexK ((valueK (start.add i)).mul 5)) lo ((valueK (start.add i)).mul 2))
        (firstLocK (indexK ((valueK (start.add i)).mul 7)) lo ((valueK (start.add i)).mul 2)) n))

/-- `segMarkK` with seeds dropped outside the window, `n` doubling rounds, no rounds at all when
`2 * p > Wm1` (only the seeds can then land in the window), and no subtraction when nothing hits. -/
@[expose] public noncomputable def segMarkCK (seg p lo Wm1 n : Nat) : Nat :=
  ((p.mul 2).ble Wm1).rec
    (clearHitK seg
      (seg.land ((seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
        (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1))))
    (clearHitK seg
      (seg.land (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
        (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n)))

/-- `segLoopK` marking with `segMarkCK`. -/
@[expose] public noncomputable def segLoopCK (s lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK s (start.add i)).rec b (segMarkCK b (valueK (start.add i)) lo Wm1 n)

/-! ### A thirty wheel, as a prototype

The window above holds one bit per integer coprime to 6, two residues in every six. A wheel of
thirty holds eight residues in every thirty, so the same bit count covers 3.75 times as many
integers instead of 3. Cost here is per divisor rather than per multiple — a divisor's mask is
built the full width of the window whichever divisor it is — so a window that reaches further for
the same divisors is worth measuring. Against that, a divisor now has eight progressions where it
had two, so its mask takes eight seeds.

Nothing below is proved sound. It exists to be timed against the wheel of six at the same width,
which the kernel can do honestly because it still checks every literal: a batch equation here says
`segLoop30CK … = literal`, and the emitter twin producing that literal is not trusted. Whether a
window of this shape sieves correctly is a separate question, not answered here. -/

/-- The eight residues coprime to 30, five bits each: 1, 7, 11, 13, 17, 19, 23, 29. -/
@[expose] public def wheel30OffsK : Nat := 1021784272097

/-- Where each residue modulo 30 sits among those eight, three bits each. Entries for residues
sharing a factor with 30 are never read. -/
@[expose] public def wheel30RankK : Nat := 1083201076879154698854072320

/-- The eight multipliers a divisor's progressions start from: 7, 11, 13, 17, 19, 23, 29, 31,
five bits each. These are the residues coprime to 30 above 1, so `p` itself is not crossed out. -/
@[expose] public def wheel30MulK : Nat := 1097082647911

/-- The `k`th integer coprime to 30. -/
@[expose] public noncomputable def value30K (k : Nat) : Nat :=
  Nat.add (Nat.mul 30 (Nat.div k 8))
    (Nat.land (Nat.shiftRight wheel30OffsK (Nat.mul 5 (Nat.mod k 8))) 31)

/-- Where an integer coprime to 30 sits in that enumeration. -/
@[expose] public noncomputable def index30K (q : Nat) : Nat :=
  Nat.add (Nat.mul 8 (Nat.div q 30))
    (Nat.land (Nat.shiftRight wheel30RankK (Nat.mul 3 (Nat.mod q 30))) 7)

/-- The eight seed bits of `p` in a window starting at wheel index `lo`, joined. A divisor's
pattern repeats every 30 `p`, which is `8 * p` positions of this wheel. -/
@[expose] public noncomputable def seeds30K (p lo M : Nat) : Nat :=
  Nat.rec 0
    (fun j a =>
      a.lor (seedK (firstLocK
        (index30K (p.mul (Nat.land (Nat.shiftRight wheel30MulK (Nat.mul 5 j)) 31)))
        lo (p.mul 8)) M))
    8

/-- `buildMaskCK` for the wheel of thirty: the same doubling, from eight seeds, with the period
`8 * p` in place of `2 * p`. -/
@[expose] public noncomputable def buildMask30CK (p M lo n : Nat) : Nat :=
  Nat.rec
    (seeds30K p lo M)
    (fun i Mk =>
      ((p.shiftLeft (i.succ.add 2)).ble M).rec Mk
        (Mk.lor (Mk.shiftLeft (p.shiftLeft (i.succ.add 2)))))
    n

/-- `segMarkCK` for the wheel of thirty. -/
@[expose] public noncomputable def segMark30CK (seg p lo Wm1 n : Nat) : Nat :=
  ((p.mul 8).ble Wm1).rec
    (clearHitK seg ((seeds30K p lo Wm1).land seg))
    (clearHitK seg ((buildMask30CK p Wm1 lo n).land seg))

/-- `segLoopCK` for the wheel of thirty. The divisors are still read from the wheel-of-six base
sieve, since how the base primes are enumerated is independent of the window's wheel. -/
@[expose] public noncomputable def segLoop30CK (s lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK s (start.add i)).rec b (segMark30CK b (valueK (start.add i)) lo Wm1 n)

/-- `segLoopK` reading the base primes from a slice `c` of the base sieve: bit `i` of `c` stands for
base index `start + i`. -/
@[expose] public noncomputable def segLoopSK (c lo Wm1 seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkK b (valueK (start.add i)) lo Wm1)

/-- `segLoopSK` marking with `segMarkCK`. -/
@[expose] public noncomputable def segLoopSCK (c lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkCK b (valueK (start.add i)) lo Wm1 n)

/-- The number of terms of `A, A + 2p, A + 4p, …` that can land at or below `M`. -/
@[expose] public noncomputable def termsK (p M : Nat) : Nat :=
  (M.div (p.mul 2)).succ

/-- `buildMaskCK`'s progression built to exactly `termsK p M` terms, by reading the binary digits
of that count from the top down: each round doubles the terms so far, and a set digit adds one more
copy of the seeds. The mask's top bit is then within `2*p` of `M`, where the doubling rounds of
`buildMaskCK` can carry it to nearly `2*M`. `n` counts digits, so `n` must reach the width of
`termsK p M`. -/
@[expose] public noncomputable def buildMaskNK (p M A B n : Nat) : Nat :=
  Nat.rec
    0
    (fun i Mk =>
      let c := (termsK p M).shiftRight (n.sub i)
      let doubled := Mk.lor (Mk.shiftLeft ((p.mul 2).mul c))
      (Nat.beq (((termsK p M).shiftRight (n.sub i.succ)).land 1) 1).rec
        doubled
        (doubled.lor
          (((Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B)).shiftLeft ((p.mul 2).mul (c.mul 2)))))
    n

/-- The same set of positions as `buildMaskCK`, in closed form: the number whose binary digits are
`1` at every multiple of `2*p` below `2*p*k` is `(2 ^ (2*p*k) - 1) / (2 ^ (2*p) - 1)`, and
multiplying it by the two seed bits places the two progressions. No doubling history, and the top
bit lands within `2*p` of `M`. -/
@[expose] public noncomputable def buildMaskRK (p M A B : Nat) : Nat :=
  ((Nat.sub (Nat.pow 2 ((p.mul 2).mul (termsK p M))) 1).div
      (Nat.sub (Nat.pow 2 (p.mul 2)) 1)).mul
    ((Nat.shiftLeft 1 A).lor (Nat.shiftLeft 1 B))

/-! ### Sorting the large primes into slices of the window

A prime past half the window's width hits the window at most twice, yet `segMarkCK` gives it a mask
as wide as the window. These definitions take the hits of a whole batch of such primes, sorted by
which 65536-bit slice of the window they land in, and write each into its slice. The state threaded
through both folds is one number: the slice being filled in its low 65536 bits, then one bit per
position of the batch for each of the two progressions, so that a completed batch can say which
positions it accounted for. -/

/-- One entry of a slice's list: its low two bits pick which of a divisor's four possible seeds it
names, the rest is the position within the batch. The low bit of those two picks the progression
and the next steps that progression on by a further `2p`, which is what a divisor striking three or
four times needs. The entry is used only if the batch's slice says that position holds a prime and
the seed really lands in slice `k`; otherwise the state is left alone, and the missing bit in the
four tallies is what a completed batch notices. -/
@[expose] public noncomputable def entrySeedK (lo start e : Nat) : Nat :=
  Nat.add
    ((Nat.beq ((e.land 7).land 1) 0).rec
      (firstLocK (indexK ((valueK (start.add (e.shiftRight 3))).mul 7)) lo
        ((valueK (start.add (e.shiftRight 3))).mul 2))
      (firstLocK (indexK ((valueK (start.add (e.shiftRight 3))).mul 5)) lo
        ((valueK (start.add (e.shiftRight 3))).mul 2)))
    (Nat.mul ((e.land 7).shiftRight 1) ((valueK (start.add (e.shiftRight 3))).mul 2))

/-- The bit an entry adds to the tally: one per position of the batch for each of the four seeds. -/
@[expose] public noncomputable def entryTallyK (len e : Nat) : Nat :=
  Nat.add 65536 (Nat.add (e.shiftRight 3) (Nat.mul (e.land 7) len))

@[expose] public noncomputable def stripeEntryK (st c lo start k len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 3)).rec st
    ((Nat.beq ((entrySeedK lo start e).shiftRight 16) k).rec st
      (st.lor ((Nat.shiftLeft 1 ((entrySeedK lo start e).land 65535)).lor
        (Nat.shiftLeft 1 (entryTallyK len e)))))

/-- An entry of the list of seeds that fall past the end of the window: the kernel checks that it
does fall past the end, and records it in the tally so that a completed batch accounts for every
seed of every prime it holds. -/
@[expose] public noncomputable def stripeOutK (st c lo start Wm1 len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 3)).rec st
    ((Nat.blt Wm1 (entrySeedK lo start e)).rec st
      (st.lor (Nat.shiftLeft 1 (entryTallyK len e))))

/-! ### A record that closes out the rest of its progression

28.6% of the records above name a strike past the end of the window, and a screen measured that
their walk is 32% of that band's kernel time. They exist only so that the tally accounts for every
strike, which is what stops a divisor being skipped. The records below let the last in-window
record of a progression account for the strikes after it instead, so the out-of-window ones need
not be emitted at all.

A record is `flag` at bit 15, the position in bits 3 to 14, and the strike in the low three, so a
batch holds at most 4096 positions where the plain record allows 8192. That is the cost that comes
with the saving, and it has to be measured apart from it: `ZZ_Len4096` is the plain record at the
shorter length, so the three arms separate the two changes.

A flagged record earns its tail: the kernel checks that the next strike of its progression really
is past the end, and contributes nothing if it is not, so flagging early breaks the batch. -/

/-- `entrySeedK` for a record whose position is twelve bits. -/
@[expose] public noncomputable def entrySeedGK (lo start e : Nat) : Nat :=
  Nat.add
    ((Nat.beq ((e.land 7).land 1) 0).rec
      (firstLocK (indexK ((valueK (start.add ((e.shiftRight 3).land 4095))).mul 7)) lo
        ((valueK (start.add ((e.shiftRight 3).land 4095))).mul 2))
      (firstLocK (indexK ((valueK (start.add ((e.shiftRight 3).land 4095))).mul 5)) lo
        ((valueK (start.add ((e.shiftRight 3).land 4095))).mul 2)))
    (Nat.mul ((e.land 7).shiftRight 1) ((valueK (start.add ((e.shiftRight 3).land 4095))).mul 2))

/-- The tally bit of a record whose position is twelve bits. -/
@[expose] public noncomputable def entryTallyGK (len e : Nat) : Nat :=
  Nat.add 65536 (Nat.add ((e.shiftRight 3).land 4095) (Nat.mul (e.land 7) len))

/-- The tally bits of this record's strike and of every later strike of the same progression. The
lanes of one progression are two apart, so this walks `w`, `w+2`, `w+4`, `w+6` and keeps those
that exist. -/
@[expose] public noncomputable def tailTallyGK (len e : Nat) : Nat :=
  Nat.rec 0
    (fun j acc =>
      ((Nat.add (e.land 7) (Nat.mul 2 j)).ble 7).rec acc
        (acc.lor (Nat.shiftLeft 1
          (Nat.add 65536 (Nat.add ((e.shiftRight 3).land 4095)
            (Nat.mul (Nat.add (e.land 7) (Nat.mul 2 j)) len))))))
    4

/-- `stripeEntryK` where a flagged record closes out its progression. The flag is honoured only
when the next strike really is past the end of the window; otherwise the record contributes
nothing and the batch's tally comes up short. -/
@[expose] public noncomputable def stripeEntryGK (st c lo start Wm1 k len e : Nat) : Nat :=
  (testBitK c ((e.shiftRight 3).land 4095)).rec st
    ((Nat.beq ((entrySeedGK lo start e).shiftRight 16) k).rec st
      (st.lor ((Nat.shiftLeft 1 ((entrySeedGK lo start e).land 65535)).lor
        ((Nat.beq (e.shiftRight 15) 0).rec
          ((Nat.ble (Nat.add (entrySeedGK lo start e)
            ((valueK (start.add ((e.shiftRight 3).land 4095))).mul 2)) Wm1).rec
              (tailTallyGK len e) 0)
          (Nat.shiftLeft 1 (entryTallyGK len e))))))

/-- The entries of one slice's list, through the closing-out record. -/
@[expose] public noncomputable def stripeSlotGK (c lo start Wm1 k len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeEntryGK s c lo start Wm1 k len ((slot.shiftRight (j.mul 16)).land 65535)

/-- `stripeUpToK` through the closing-out record. There is no out-of-window list: slice `np` is
gone, since a progression's tail is accounted for by its last in-window record. -/
@[expose] public noncomputable def stripeUpToGK
    (c lo start len W Wm1 slotW Ls Cs n : Nat) : Nat :=
  n.rec 0 fun k asm =>
    let slot : Nat := (Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)
    let cnt : Nat := (Cs.shiftRight (k.mul 16)).land 65535
    let st : Nat := stripeSlotGK c lo start Wm1 k len slot cnt 0
    (asm.lor ((st.land (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (k.mul 65536))).lor
      ((st.shiftRight 65536).shiftLeft W)

/-- The assembled number of a batch whose records close out their own progressions. -/
@[expose] public noncomputable def stripeBatchGK
    (c lo start len W Wm1 slotW Ls Cs np : Nat) : Nat :=
  stripeUpToGK c lo start len W Wm1 slotW Ls Cs np

/-- The same seed as `entrySeedK`, written so that the divisor's value and its stride each appear
once rather than once per use. Timing only, until a measurement says whether the kernel cares. -/
@[expose] public noncomputable def entrySeedTK (lo start e : Nat) : Nat :=
  let w : Nat := e.land 7
  let p : Nat := valueK (start.add (e.shiftRight 3))
  let d : Nat := p.mul 2
  Nat.add
    ((Nat.beq (w.land 1) 0).rec
      (firstLocK (indexK (p.mul 7)) lo d)
      (firstLocK (indexK (p.mul 5)) lo d))
    (Nat.mul (w.shiftRight 1) d)

/-- `stripeEntryK` with the seed written once rather than once for the slice test and once for the
bit it sets. -/
@[expose] public noncomputable def stripeEntryTK (st c lo start k len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 3)).rec st
    (let s : Nat := entrySeedTK lo start e
     (Nat.beq (s.shiftRight 16) k).rec st
       (st.lor ((Nat.shiftLeft 1 (s.land 65535)).lor
         (Nat.shiftLeft 1 (entryTallyK len e)))))

/-- `stripeOutK` through the shared-subterm seed. -/
@[expose] public noncomputable def stripeOutTK (st c lo start Wm1 len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 3)).rec st
    ((Nat.blt Wm1 (entrySeedTK lo start e)).rec st
      (st.lor (Nat.shiftLeft 1 (entryTallyK len e))))

/-- The entries of one slice's list, packed 16 bits each. -/
@[expose] public noncomputable def stripeSlotK (c lo start k len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeEntryK s c lo start k len ((slot.shiftRight (j.mul 16)).land 65535)

/-- The entries of the out-of-window list. -/
@[expose] public noncomputable def stripeOutSlotK (c lo start Wm1 len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeOutK s c lo start Wm1 len ((slot.shiftRight (j.mul 16)).land 65535)

/-- Every slice of the window in turn, each filled from its own list and then written into its
place in the mask, with the tallies carried above the mask. `np` is how many slices the window
holds, so slice `np` is the list of seeds that fall past the window's end. -/
@[expose] public noncomputable def stripeUpToK
    (c lo start len W Wm1 slotW Ls Cs np n : Nat) : Nat :=
  n.rec 0 fun k asm =>
    let slot : Nat := (Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)
    let cnt : Nat := (Cs.shiftRight (k.mul 16)).land 65535
    let st : Nat := (Nat.beq k np).rec
      (stripeSlotK c lo start k len slot cnt 0)
      (stripeOutSlotK c lo start Wm1 len slot cnt 0)
    (asm.lor ((st.land (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (k.mul 65536))).lor
      ((st.shiftRight 65536).shiftLeft W)

/-- Every slice of the window, which is `stripeUpToK` run to the end: the `np` slices of the window
and then the list of seeds past its end. -/
@[expose] public noncomputable def stripeBatchK (c lo start len W Wm1 slotW Ls Cs np : Nat) : Nat :=
  stripeUpToK c lo start len W Wm1 slotW Ls Cs np (np + 1)

/-! ### Sixteen records to a divisor

The octave below the one above: a divisor whose eightfold fits the window and whose sixteenfold does
not strikes at most eight times on each progression, so sixteen records name every strike. These
definitions are the eight-record ones with the lane field widened from three bits to four. A record
is still sixteen bits, so the extra lane bit comes out of the position, which caps a batch at 4096
divisors where the eight-record route takes 8192. The tally is the same width either way, since
sixteen lanes of 4096 and eight of 8192 both come to 65536 bits. -/

/-- `entrySeedK` with a four-bit lane: the low bit still picks the progression and the other three
step it on, so a record reaches the eighth strike rather than the fourth. -/
@[expose] public noncomputable def entrySeedHK (lo start e : Nat) : Nat :=
  Nat.add
    ((Nat.beq ((e.land 15).land 1) 0).rec
      (firstLocK (indexK ((valueK (start.add (e.shiftRight 4))).mul 7)) lo
        ((valueK (start.add (e.shiftRight 4))).mul 2))
      (firstLocK (indexK ((valueK (start.add (e.shiftRight 4))).mul 5)) lo
        ((valueK (start.add (e.shiftRight 4))).mul 2)))
    (Nat.mul ((e.land 15).shiftRight 1) ((valueK (start.add (e.shiftRight 4))).mul 2))

/-- The bit a four-bit-lane record adds to the tally: one per position for each of sixteen lanes. -/
@[expose] public noncomputable def entryTallyHK (len e : Nat) : Nat :=
  Nat.add 65536 (Nat.add (e.shiftRight 4) (Nat.mul (e.land 15) len))

/-- `stripeEntryK` over four-bit lanes. -/
@[expose] public noncomputable def stripeEntryHK (st c lo start k len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 4)).rec st
    ((Nat.beq ((entrySeedHK lo start e).shiftRight 16) k).rec st
      (st.lor ((Nat.shiftLeft 1 ((entrySeedHK lo start e).land 65535)).lor
        (Nat.shiftLeft 1 (entryTallyHK len e)))))

/-- `stripeOutK` over four-bit lanes. -/
@[expose] public noncomputable def stripeOutHK (st c lo start Wm1 len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 4)).rec st
    ((Nat.blt Wm1 (entrySeedHK lo start e)).rec st
      (st.lor (Nat.shiftLeft 1 (entryTallyHK len e))))

/-- The entries of one slice's list, packed 16 bits each, over four-bit lanes. -/
@[expose] public noncomputable def stripeSlotHK (c lo start k len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeEntryHK s c lo start k len ((slot.shiftRight (j.mul 16)).land 65535)

/-- The entries of the out-of-window list, over four-bit lanes. -/
@[expose] public noncomputable def stripeOutSlotHK (c lo start Wm1 len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeOutHK s c lo start Wm1 len ((slot.shiftRight (j.mul 16)).land 65535)

/-- `stripeUpToK` over four-bit lanes. -/
@[expose] public noncomputable def stripeUpToHK
    (c lo start len W Wm1 slotW Ls Cs np n : Nat) : Nat :=
  n.rec 0 fun k asm =>
    let slot : Nat := (Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)
    let cnt : Nat := (Cs.shiftRight (k.mul 16)).land 65535
    let st : Nat := (Nat.beq k np).rec
      (stripeSlotHK c lo start k len slot cnt 0)
      (stripeOutSlotHK c lo start Wm1 len slot cnt 0)
    (asm.lor ((st.land (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (k.mul 65536))).lor
      ((st.shiftRight 65536).shiftLeft W)

/-- `stripeBatchK` over four-bit lanes. -/
@[expose] public noncomputable def stripeBatchHK
    (c lo start len W Wm1 slotW Ls Cs np : Nat) : Nat :=
  stripeUpToHK c lo start len W Wm1 slotW Ls Cs np (np + 1)

/-! ### Thirty-two records to a divisor

One octave further down again, where a divisor's sixteenfold fits the window and its thirty-twofold
does not. The lane takes five bits of a record and the position eleven, so a batch holds 2048
divisors. The tally stays 65536 bits wide, as it does at eight lanes and at sixteen, because the
lane count times the batch length is 65536 in all three. -/

/-- `entrySeedK` with a five-bit lane. -/
@[expose] public noncomputable def entrySeedXK (lo start e : Nat) : Nat :=
  Nat.add
    ((Nat.beq ((e.land 31).land 1) 0).rec
      (firstLocK (indexK ((valueK (start.add (e.shiftRight 5))).mul 7)) lo
        ((valueK (start.add (e.shiftRight 5))).mul 2))
      (firstLocK (indexK ((valueK (start.add (e.shiftRight 5))).mul 5)) lo
        ((valueK (start.add (e.shiftRight 5))).mul 2)))
    (Nat.mul ((e.land 31).shiftRight 1) ((valueK (start.add (e.shiftRight 5))).mul 2))

/-- The bit a five-bit-lane record adds to the tally. -/
@[expose] public noncomputable def entryTallyXK (len e : Nat) : Nat :=
  Nat.add 65536 (Nat.add (e.shiftRight 5) (Nat.mul (e.land 31) len))

/-- `stripeEntryK` over five-bit lanes. -/
@[expose] public noncomputable def stripeEntryXK (st c lo start k len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 5)).rec st
    ((Nat.beq ((entrySeedXK lo start e).shiftRight 16) k).rec st
      (st.lor ((Nat.shiftLeft 1 ((entrySeedXK lo start e).land 65535)).lor
        (Nat.shiftLeft 1 (entryTallyXK len e)))))

/-- `stripeOutK` over five-bit lanes. -/
@[expose] public noncomputable def stripeOutXK (st c lo start Wm1 len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 5)).rec st
    ((Nat.blt Wm1 (entrySeedXK lo start e)).rec st
      (st.lor (Nat.shiftLeft 1 (entryTallyXK len e))))

/-- The entries of one slice's list, packed 16 bits each, over five-bit lanes. -/
@[expose] public noncomputable def stripeSlotXK (c lo start k len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeEntryXK s c lo start k len ((slot.shiftRight (j.mul 16)).land 65535)

/-- The entries of the out-of-window list, over five-bit lanes. -/
@[expose] public noncomputable def stripeOutSlotXK (c lo start Wm1 len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeOutXK s c lo start Wm1 len ((slot.shiftRight (j.mul 16)).land 65535)

/-- `stripeUpToK` over five-bit lanes. -/
@[expose] public noncomputable def stripeUpToXK
    (c lo start len W Wm1 slotW Ls Cs np n : Nat) : Nat :=
  n.rec 0 fun k asm =>
    let slot : Nat := (Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)
    let cnt : Nat := (Cs.shiftRight (k.mul 16)).land 65535
    let st : Nat := (Nat.beq k np).rec
      (stripeSlotXK c lo start k len slot cnt 0)
      (stripeOutSlotXK c lo start Wm1 len slot cnt 0)
    (asm.lor ((st.land (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (k.mul 65536))).lor
      ((st.shiftRight 65536).shiftLeft W)

/-- `stripeBatchK` over five-bit lanes. -/
@[expose] public noncomputable def stripeBatchXK
    (c lo start len W Wm1 slotW Ls Cs np : Nat) : Nat :=
  stripeUpToXK c lo start len W Wm1 slotW Ls Cs np (np + 1)

/-! ### The sorted batch with the lane width left open

The three families above bake the lane width into every definition, so each band width has meant a
fresh copy of eight definitions and of the proofs over them. These take the width as an argument.

The point of them is the four `rfl`s at the end: the families above are *definitionally* these at
`lw = 3`, `4` and `5`. So a proof about `stripeBatchLK` applies to the band the sieve runs today
without that band's kernel terms changing at all, and the emitter goes on naming `stripeBatchK`
exactly as it does now. Nothing has to be measured again to use them. -/

/-- The mask that keeps a record's lane: `2 ^ lw - 1`. -/
@[expose] public noncomputable def laneMaskK (lw : Nat) : Nat :=
  Nat.sub (Nat.shiftLeft 1 lw) 1

/-- `entrySeedK` with the lane width left open. -/
@[expose] public noncomputable def entrySeedLK (lw lo start e : Nat) : Nat :=
  Nat.add
    ((Nat.beq ((e.land (laneMaskK lw)).land 1) 0).rec
      (firstLocK (indexK ((valueK (start.add (e.shiftRight lw))).mul 7)) lo
        ((valueK (start.add (e.shiftRight lw))).mul 2))
      (firstLocK (indexK ((valueK (start.add (e.shiftRight lw))).mul 5)) lo
        ((valueK (start.add (e.shiftRight lw))).mul 2)))
    (Nat.mul ((e.land (laneMaskK lw)).shiftRight 1)
      ((valueK (start.add (e.shiftRight lw))).mul 2))

/-- `entryTallyK` with the lane width left open. -/
@[expose] public noncomputable def entryTallyLK (lw len e : Nat) : Nat :=
  Nat.add 65536 (Nat.add (e.shiftRight lw) (Nat.mul (e.land (laneMaskK lw)) len))

/-- `stripeEntryK` with the lane width left open. -/
@[expose] public noncomputable def stripeEntryLK (lw st c lo start k len e : Nat) : Nat :=
  (testBitK c (e.shiftRight lw)).rec st
    ((Nat.beq ((entrySeedLK lw lo start e).shiftRight 16) k).rec st
      (st.lor ((Nat.shiftLeft 1 ((entrySeedLK lw lo start e).land 65535)).lor
        (Nat.shiftLeft 1 (entryTallyLK lw len e)))))

/-- `stripeOutK` with the lane width left open. -/
@[expose] public noncomputable def stripeOutLK (lw st c lo start Wm1 len e : Nat) : Nat :=
  (testBitK c (e.shiftRight lw)).rec st
    ((Nat.blt Wm1 (entrySeedLK lw lo start e)).rec st
      (st.lor (Nat.shiftLeft 1 (entryTallyLK lw len e))))

/-- `stripeSlotK` with the lane width left open. -/
@[expose] public noncomputable def stripeSlotLK (lw c lo start k len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeEntryLK lw s c lo start k len ((slot.shiftRight (j.mul 16)).land 65535)

/-- `stripeOutSlotK` with the lane width left open. -/
@[expose] public noncomputable def stripeOutSlotLK
    (lw c lo start Wm1 len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeOutLK lw s c lo start Wm1 len ((slot.shiftRight (j.mul 16)).land 65535)

/-- `stripeUpToK` with the lane width left open. -/
@[expose] public noncomputable def stripeUpToLK
    (lw c lo start len W Wm1 slotW Ls Cs np n : Nat) : Nat :=
  n.rec 0 fun k asm =>
    let slot : Nat := (Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)
    let cnt : Nat := (Cs.shiftRight (k.mul 16)).land 65535
    let st : Nat := (Nat.beq k np).rec
      (stripeSlotLK lw c lo start k len slot cnt 0)
      (stripeOutSlotLK lw c lo start Wm1 len slot cnt 0)
    (asm.lor ((st.land (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (k.mul 65536))).lor
      ((st.shiftRight 65536).shiftLeft W)

/-- `stripeBatchK` with the lane width left open. -/
@[expose] public noncomputable def stripeBatchLK
    (lw c lo start len W Wm1 slotW Ls Cs np : Nat) : Nat :=
  stripeUpToLK lw c lo start len W Wm1 slotW Ls Cs np (np + 1)

/-- The three-bit family is this one at `lw = 3`, definitionally. -/
public theorem stripeBatchLK_three {c lo start len W Wm1 slotW Ls Cs np : Nat} :
    stripeBatchLK 3 c lo start len W Wm1 slotW Ls Cs np
      = stripeBatchK c lo start len W Wm1 slotW Ls Cs np := rfl

/-- The four-bit family is this one at `lw = 4`, definitionally. -/
public theorem stripeBatchLK_four {c lo start len W Wm1 slotW Ls Cs np : Nat} :
    stripeBatchLK 4 c lo start len W Wm1 slotW Ls Cs np
      = stripeBatchHK c lo start len W Wm1 slotW Ls Cs np := rfl

/-- The five-bit family is this one at `lw = 5`, definitionally. -/
public theorem stripeBatchLK_five {c lo start len W Wm1 slotW Ls Cs np : Nat} :
    stripeBatchLK 5 c lo start len W Wm1 slotW Ls Cs np
      = stripeBatchXK c lo start len W Wm1 slotW Ls Cs np := rfl

/-- The entries of one slice's list, through the shared-subterm entry. -/
@[expose] public noncomputable def stripeSlotTK (c lo start k len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeEntryTK s c lo start k len ((slot.shiftRight (j.mul 16)).land 65535)

/-- The entries of the out-of-window list, through the shared-subterm entry. -/
@[expose] public noncomputable def stripeOutSlotTK (c lo start Wm1 len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeOutTK s c lo start Wm1 len ((slot.shiftRight (j.mul 16)).land 65535)

/-- `stripeUpToK` through the shared-subterm entry. -/
@[expose] public noncomputable def stripeUpToTK
    (c lo start len W Wm1 slotW Ls Cs np n : Nat) : Nat :=
  n.rec 0 fun k asm =>
    let slot : Nat := (Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)
    let cnt : Nat := (Cs.shiftRight (k.mul 16)).land 65535
    let st : Nat := (Nat.beq k np).rec
      (stripeSlotTK c lo start k len slot cnt 0)
      (stripeOutSlotTK c lo start Wm1 len slot cnt 0)
    (asm.lor ((st.land (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (k.mul 65536))).lor
      ((st.shiftRight 65536).shiftLeft W)

/-- The same assembled number as `stripeBatchK`, reached with each shared subterm of a record
written once. The two agree by computation, so a timing pair over the same divisors is the cost of
the repeated subterms on its own. -/
@[expose] public noncomputable def stripeBatchTK
    (c lo start len W Wm1 slotW Ls Cs np : Nat) : Nat :=
  stripeUpToTK c lo start len W Wm1 slotW Ls Cs np (np + 1)

/-! ### Naming a record's shared quantities by their value

`stripeBatchTK` above writes each repeated subterm of a record once, with `let`. That left the
work unchanged, which is consistent with the kernel substituting a `let` rather than evaluating
it: the two forms then reduce through the same terms. The definitions below instead pass each
shared quantity through `forceK`, whose `Nat.rec` evaluates it before the body sees it, so the
body is handed a value. Whether that changes anything is for a timing pair to say; they compute
the same number as `stripeBatchK` either way, and the kernel checks it. -/

/-- `f x`, with `x` evaluated first. `Nat.rec` reduces its major premise before choosing a branch,
so the body receives a value in place of the term that computes it. -/
@[expose] public noncomputable def forceK (x : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (f Nat.zero) (fun n _ => f n.succ) x

/-- `forceK` names its argument and nothing else. -/
public theorem forceK_eq {x : Nat} {f : Nat → Nat} : forceK x f = f x := by
  cases x <;> rfl

/-- `entrySeedK` with the record's position and the divisor it names passed through `forceK`, so
that a divisor's several records present the same value rather than the same unevaluated term. -/
@[expose] public noncomputable def entrySeedFK (lo start e : Nat) : Nat :=
  forceK (e.shiftRight 3) fun i =>
    forceK (valueK (start.add i)) fun p =>
      Nat.add
        ((Nat.beq ((e.land 7).land 1) 0).rec
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 5)) lo (p.mul 2)))
        (Nat.mul ((e.land 7).shiftRight 1) (p.mul 2))

/-- `stripeEntryK` through `entrySeedFK`, with the seed itself forced so that the slice test and
the bit it sets read one value. -/
@[expose] public noncomputable def stripeEntryFK (st c lo start k len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 3)).rec st
    (forceK (entrySeedFK lo start e) fun s =>
      (Nat.beq (s.shiftRight 16) k).rec st
        (st.lor ((Nat.shiftLeft 1 (s.land 65535)).lor
          (Nat.shiftLeft 1 (entryTallyK len e)))))

/-- `stripeOutK` through `entrySeedFK`. -/
@[expose] public noncomputable def stripeOutFK (st c lo start Wm1 len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 3)).rec st
    ((Nat.blt Wm1 (entrySeedFK lo start e)).rec st
      (st.lor (Nat.shiftLeft 1 (entryTallyK len e))))

/-- The entries of one slice's list, through the forced entry. -/
@[expose] public noncomputable def stripeSlotFK (c lo start k len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeEntryFK s c lo start k len ((slot.shiftRight (j.mul 16)).land 65535)

/-- The entries of the out-of-window list, through the forced entry. -/
@[expose] public noncomputable def stripeOutSlotFK (c lo start Wm1 len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeOutFK s c lo start Wm1 len ((slot.shiftRight (j.mul 16)).land 65535)

/-- `stripeUpToK` through the forced entry. -/
@[expose] public noncomputable def stripeUpToFK
    (c lo start len W Wm1 slotW Ls Cs np n : Nat) : Nat :=
  n.rec 0 fun k asm =>
    let slot : Nat := (Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)
    let cnt : Nat := (Cs.shiftRight (k.mul 16)).land 65535
    let st : Nat := (Nat.beq k np).rec
      (stripeSlotFK c lo start k len slot cnt 0)
      (stripeOutSlotFK c lo start Wm1 len slot cnt 0)
    (asm.lor ((st.land (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (k.mul 65536))).lor
      ((st.shiftRight 65536).shiftLeft W)

/-- The same assembled number as `stripeBatchK`, with each record's shared quantities named by
value rather than by the term computing them. -/
@[expose] public noncomputable def stripeBatchFK
    (c lo start len W Wm1 slotW Ls Cs np : Nat) : Nat :=
  stripeUpToFK c lo start len W Wm1 slotW Ls Cs np (np + 1)

/-! ### Dispatching strikes into a tree instead of sorting them into records

The sorted design hands the kernel a list of records and has it place each one. This asks whether
the kernel can find the places itself as cheaply: it walks the batch's positions as the unsorted
path does, computes a divisor's value and stride once and derives all its strikes from them, and
puts each strike into one of 64 leaves by dispatching on the six bits of the leaf number. There are
no records, no sort, and no tally, so a batch's whole obligation is one equation against the
assembled mask.

Timing only and no proofs: the question is whether a `Prod`-valued accumulator through `Nat.rec`
costs what the record fold costs, and nothing in this project has measured that. If it wins, the
proofs are `testBit_treeFold` mirroring `testBit_segAccLoopSK_wide` plus one flatten lemma per
level, and they retire the record and tally lemmas for this path. -/

/-- A tree of 64 leaves, each a slice of the window. -/
public abbrev Lvl1 := Nat × Nat
/-- Two slices. -/
public abbrev Lvl2 := Lvl1 × Lvl1
/-- Four slices. -/
public abbrev Lvl3 := Lvl2 × Lvl2
/-- Eight slices. -/
public abbrev Lvl4 := Lvl3 × Lvl3
/-- Sixteen slices. -/
public abbrev Lvl5 := Lvl4 × Lvl4
/-- Thirty-two slices. -/
public abbrev Lvl6 := Lvl5 × Lvl5
/-- Sixty-four slices, one per 65536 bits of a 4194304-bit window. -/
public abbrev Lvl7 := Lvl6 × Lvl6

/-- Set bit `b` of the leaf `k` names, dispatching on the low bit of `k`. -/
@[expose] public noncomputable def upd1 (t : Lvl1) (k b : Nat) : Lvl1 :=
  (Nat.beq (k.land 1) 0).rec (t.1, t.2.lor (Nat.shiftLeft 1 b))
    (t.1.lor (Nat.shiftLeft 1 b), t.2)

/-- One level up: dispatch on bit 1 of `k`. -/
@[expose] public noncomputable def upd2 (t : Lvl2) (k b : Nat) : Lvl2 :=
  (Nat.beq ((k.shiftRight 1).land 1) 0).rec (t.1, upd1 t.2 k b) (upd1 t.1 k b, t.2)

/-- Dispatch on bit 2 of `k`. -/
@[expose] public noncomputable def upd3 (t : Lvl3) (k b : Nat) : Lvl3 :=
  (Nat.beq ((k.shiftRight 2).land 1) 0).rec (t.1, upd2 t.2 k b) (upd2 t.1 k b, t.2)

/-- Dispatch on bit 3 of `k`. -/
@[expose] public noncomputable def upd4 (t : Lvl4) (k b : Nat) : Lvl4 :=
  (Nat.beq ((k.shiftRight 3).land 1) 0).rec (t.1, upd3 t.2 k b) (upd3 t.1 k b, t.2)

/-- Dispatch on bit 4 of `k`. -/
@[expose] public noncomputable def upd5 (t : Lvl5) (k b : Nat) : Lvl5 :=
  (Nat.beq ((k.shiftRight 4).land 1) 0).rec (t.1, upd4 t.2 k b) (upd4 t.1 k b, t.2)

/-- Dispatch on bit 5 of `k`. -/
@[expose] public noncomputable def upd6 (t : Lvl6) (k b : Nat) : Lvl6 :=
  (Nat.beq ((k.shiftRight 5).land 1) 0).rec (t.1, upd5 t.2 k b) (upd5 t.1 k b, t.2)

/-- Dispatch on bit 6 of `k`, the top of a 64-leaf tree. -/
@[expose] public noncomputable def upd7 (t : Lvl7) (k b : Nat) : Lvl7 :=
  (Nat.beq ((k.shiftRight 6).land 1) 0).rec (t.1, upd6 t.2 k b) (upd6 t.1 k b, t.2)

/-! ### Joining a whole leaf

`upd1` to `upd7` carry one strike down seven levels. A batch whose strikes are grouped by leaf can
instead build a leaf and join it once, so the descent is paid per leaf rather than per strike.
These are `upd1` to `upd7` with the leaf value in place of `Nat.shiftLeft 1 b`. -/

/-- Join a whole leaf at the bottom level, dispatching on bit 0 of `k`. -/
@[expose] public noncomputable def updL1 (t : Lvl1) (k v : Nat) : Lvl1 :=
  (Nat.beq (k.land 1) 0).rec (t.1, t.2.lor v) (t.1.lor v, t.2)

/-- Dispatch on bit 1 of `k`. -/
@[expose] public noncomputable def updL2 (t : Lvl2) (k v : Nat) : Lvl2 :=
  (Nat.beq ((k.shiftRight 1).land 1) 0).rec (t.1, updL1 t.2 k v) (updL1 t.1 k v, t.2)

/-- Dispatch on bit 2 of `k`. -/
@[expose] public noncomputable def updL3 (t : Lvl3) (k v : Nat) : Lvl3 :=
  (Nat.beq ((k.shiftRight 2).land 1) 0).rec (t.1, updL2 t.2 k v) (updL2 t.1 k v, t.2)

/-- Dispatch on bit 3 of `k`. -/
@[expose] public noncomputable def updL4 (t : Lvl4) (k v : Nat) : Lvl4 :=
  (Nat.beq ((k.shiftRight 3).land 1) 0).rec (t.1, updL3 t.2 k v) (updL3 t.1 k v, t.2)

/-- Dispatch on bit 4 of `k`. -/
@[expose] public noncomputable def updL5 (t : Lvl5) (k v : Nat) : Lvl5 :=
  (Nat.beq ((k.shiftRight 4).land 1) 0).rec (t.1, updL4 t.2 k v) (updL4 t.1 k v, t.2)

/-- Dispatch on bit 5 of `k`. -/
@[expose] public noncomputable def updL6 (t : Lvl6) (k v : Nat) : Lvl6 :=
  (Nat.beq ((k.shiftRight 5).land 1) 0).rec (t.1, updL5 t.2 k v) (updL5 t.1 k v, t.2)

/-- Dispatch on bit 6 of `k`, the top of a 64-leaf tree. -/
@[expose] public noncomputable def updL7 (t : Lvl7) (k v : Nat) : Lvl7 :=
  (Nat.beq ((k.shiftRight 6).land 1) 0).rec (t.1, updL6 t.2 k v) (updL6 t.1 k v, t.2)

/-- A leaf pair as one number, the second slice above the first. -/
@[expose] public noncomputable def flat1 (t : Lvl1) : Nat :=
  t.1.lor (t.2.shiftLeft 65536)
/-- Two leaf pairs joined. -/
@[expose] public noncomputable def flat2 (t : Lvl2) : Nat :=
  (flat1 t.1).lor ((flat1 t.2).shiftLeft 131072)
/-- Four joined. -/
@[expose] public noncomputable def flat3 (t : Lvl3) : Nat :=
  (flat2 t.1).lor ((flat2 t.2).shiftLeft 262144)
/-- Eight joined. -/
@[expose] public noncomputable def flat4 (t : Lvl4) : Nat :=
  (flat3 t.1).lor ((flat3 t.2).shiftLeft 524288)
/-- Sixteen joined. -/
@[expose] public noncomputable def flat5 (t : Lvl5) : Nat :=
  (flat4 t.1).lor ((flat4 t.2).shiftLeft 1048576)
/-- Thirty-two joined. -/
@[expose] public noncomputable def flat6 (t : Lvl6) : Nat :=
  (flat5 t.1).lor ((flat5 t.2).shiftLeft 2097152)
/-- The whole tree as the assembled mask. -/
@[expose] public noncomputable def flat7 (t : Lvl7) : Nat :=
  (flat6 t.1).lor ((flat6 t.2).shiftLeft 4194304)

/-- Two empty slices. Built level by level rather than as one nested literal, so that
`flat7 zero7 = 0` is provable by seven one-line lemmas; a literal leaves projections that no
rewrite reduces. Timing found no difference between the two forms. -/
@[expose] public noncomputable def zero1 : Lvl1 := (0, 0)
/-- Four. -/
@[expose] public noncomputable def zero2 : Lvl2 := (zero1, zero1)
/-- Eight. -/
@[expose] public noncomputable def zero3 : Lvl3 := (zero2, zero2)
/-- Sixteen. -/
@[expose] public noncomputable def zero4 : Lvl4 := (zero3, zero3)
/-- Thirty-two. -/
@[expose] public noncomputable def zero5 : Lvl5 := (zero4, zero4)
/-- Sixty-four, which spans the window. -/
@[expose] public noncomputable def zero6 : Lvl6 := (zero5, zero5)

/-- An empty tree of 128 leaves. -/
@[expose] public noncomputable def zero7 : Lvl7 := (zero6, zero6)

/-- Put one strike into the tree, or leave it alone where the strike passes the window's end. -/
@[expose] public noncomputable def putK (t : Lvl7) (Wm1 s : Nat) : Lvl7 :=
  (Nat.blt Wm1 s).rec (upd7 t (s.shiftRight 16) (s.land 65535)) t

/-- Every strike of one divisor, its value and stride computed once and the eight strikes derived
from them. -/
@[expose] public noncomputable def treeDivK (t : Lvl7) (lo Wm1 p : Nat) : Lvl7 :=
  let d : Nat := p.mul 2
  let A : Nat := firstLocK (indexK (p.mul 5)) lo d
  let B : Nat := firstLocK (indexK (p.mul 7)) lo d
  putK (putK (putK (putK (putK (putK (putK (putK t Wm1 A) Wm1 B)
    Wm1 (A.add d)) Wm1 (B.add d))
    Wm1 (A.add (d.mul 2))) Wm1 (B.add (d.mul 2)))
    Wm1 (A.add (d.mul 3))) Wm1 (B.add (d.mul 3))

/-- Walk the batch's positions, putting every strike of every divisor the slice names into the
tree. -/
@[expose] public noncomputable def treeFoldK (c lo Wm1 start len : Nat) : Lvl7 :=
  len.rec zero7 fun i t =>
    (testBitK c i).rec t (treeDivK t lo Wm1 (valueK (start.add i)))

/-- The batch's assembled mask, found by the kernel rather than handed to it. -/
@[expose] public noncomputable def treeBatchK (c lo Wm1 start len : Nat) : Nat :=
  flat7 (treeFoldK c lo Wm1 start len)

/-- The two strikes of a divisor whose double already passes the window's end. Deriving eight and
discarding six cost 4.9 percent of kernel over that band, so the count a band needs is a parameter
of the design rather than a constant. -/
@[expose] public noncomputable def treeDiv2K (t : Lvl7) (lo Wm1 p : Nat) : Lvl7 :=
  let d : Nat := p.mul 2
  putK (putK t Wm1 (firstLocK (indexK (p.mul 5)) lo d)) Wm1
    (firstLocK (indexK (p.mul 7)) lo d)

/-- Walk the batch, two strikes to a divisor. -/
@[expose] public noncomputable def treeFold2K (c lo Wm1 start len : Nat) : Lvl7 :=
  len.rec zero7 fun i t =>
    (testBitK c i).rec t (treeDiv2K t lo Wm1 (valueK (start.add i)))

/-- The assembled mask of a batch whose divisors strike at most twice. -/
@[expose] public noncomputable def treeBatch2K (c lo Wm1 start len : Nat) : Nat :=
  flat7 (treeFold2K c lo Wm1 start len)

/-- The two strikes of a divisor, the second taken from the first. `k` is the position the fold
walks, so the divisor is `valueK k` and `index_mul_seven` puts the second progression `2 * k + 1`
wheel positions after the first. -/
@[expose] public noncomputable def treeDiv2EK (t : Lvl7) (lo Wm1 k : Nat) : Lvl7 :=
  let d : Nat := (valueK k).mul 2
  let A : Nat := firstLocK (indexK ((valueK k).mul 5)) lo d
  putK (putK t Wm1 A) Wm1 ((A + (k * 2 + 1)) % d)

/-- Walk the batch, two strikes to a divisor, the second taken from the first. -/
@[expose] public noncomputable def treeFold2EK (c lo Wm1 start len : Nat) : Lvl7 :=
  len.rec zero7 fun i t =>
    (testBitK c i).rec t (treeDiv2EK t lo Wm1 (start.add i))

/-- The assembled mask of a batch of the widest band, each divisor's second strike taken from its
first. -/
@[expose] public noncomputable def treeBatch2EK (c lo Wm1 start len : Nat) : Nat :=
  flat7 (treeFold2EK c lo Wm1 start len)

/-- How many of a batch's positions name a divisor, found by the walk `treeFold2K` performs. This
places no strike and settles no window; it is emitted beside a batch to price the walk apart from
the strikes, since a batch of the widest band walks far more positions than it finds divisors. -/
@[expose] public noncomputable def walkCountK (c len : Nat) : Nat :=
  len.rec 0 fun i n => (testBitK c i).rec n n.succ

/-- Strikes given in leaf order, each built into its leaf and the leaf joined once. The state is
the joined tree, the leaf being built, and that leaf's index. `q` packs one 32-bit strike position
an entry, least significant first. -/
@[expose] public noncomputable def joinFoldK : Nat → Nat → Lvl7 × Nat × Nat
  | _, 0 => (zero7, 0, 0)
  | q, cnt + 1 =>
    let acc : Lvl7 × Nat × Nat := joinFoldK q cnt
    let s : Nat := (q.shiftRight (cnt.mul 32)).land 4294967295
    let k : Nat := s.shiftRight 16
    (Nat.beq k acc.2.2).rec
      (updL7 acc.1 acc.2.2 acc.2.1, Nat.shiftLeft 1 (s.land 65535), k)
      (acc.1, acc.2.1.lor (Nat.shiftLeft 1 (s.land 65535)), acc.2.2)

/-- The mask those strikes assemble, the leaf left pending joined at the end. -/
@[expose] public noncomputable def joinBatchK (q cnt : Nat) : Nat :=
  let r : Lvl7 × Nat × Nat := joinFoldK q cnt
  flat7 (updL7 r.1 r.2.2 r.2.1)

/-- The same strikes joined one at a time, which is what the tree's per-strike descent gives. -/
@[expose] public noncomputable def orStrikesK : Nat → Nat → Nat
  | _, 0 => 0
  | q, cnt + 1 =>
    (orStrikesK q cnt).lor (Nat.shiftLeft 1 ((q.shiftRight (cnt.mul 32)).land 4294967295))

/-- A batch's mask assembled from strikes given in leaf order: a leaf is built whole and joined
once, so the join is paid per leaf rather than per strike. `q` packs one 32-bit strike position an
entry, least significant first, and the state carries the joined mask, the leaf being built and
its index. Emitted beside a batch to price that grouping against the per-strike descent; it
settles no window. -/
@[expose] public noncomputable def bucketJoinK (q cnt : Nat) : Nat :=
  let r : Nat × Nat × Nat :=
    cnt.rec (0, 0, 0) fun i acc =>
      let s : Nat := (q.shiftRight (i.mul 32)).land 4294967295
      let k : Nat := s.shiftRight 16
      (Nat.beq k acc.2.2).rec
        (acc.1.lor (acc.2.1.shiftLeft (acc.2.2.mul 65536)), Nat.shiftLeft 1 (s.land 65535), k)
        (acc.1, acc.2.1.lor (Nat.shiftLeft 1 (s.land 65535)), acc.2.2)
  r.1.lor (r.2.1.shiftLeft (r.2.2.mul 65536))

/-- The sum of a batch's strike positions, found by the same arithmetic `treeDiv2K` performs and
added rather than placed. Emitted beside a batch to price that arithmetic apart from the dispatch
of each strike into its leaf. -/
@[expose] public noncomputable def seedSumK (c lo start len : Nat) : Nat :=
  len.rec 0 fun i n =>
    (testBitK c i).rec n
      (let p : Nat := valueK (start.add i)
       let d : Nat := p.mul 2
       n.add ((firstLocK (indexK (p.mul 5)) lo d).add (firstLocK (indexK (p.mul 7)) lo d)))

/-- Two consecutive windows' trees. -/
@[expose] public noncomputable def Pair7 : Type := Lvl7 × Lvl7

/-- The seed offset in the next window, from the offset in this one. Correct where the stride `m`
is at least the window width `W`, which holds for every divisor with `Wm1 < 2 * p`. -/
@[expose] public def stepLocK (x W m : Nat) : Nat :=
  (Nat.blt x W).rec (Nat.sub x W) (Nat.sub (Nat.add x m) W)

/-- One divisor's two strikes in each of two consecutive windows, deriving the offsets for the
first window and stepping them to the second. -/
@[expose] public noncomputable def treeDiv2PairK (t : Pair7) (lo Wm1 W p : Nat) : Pair7 :=
  let d : Nat := p.mul 2
  let a : Nat := firstLocK (indexK (p.mul 5)) lo d
  let b : Nat := firstLocK (indexK (p.mul 7)) lo d
  (putK (putK t.1 Wm1 a) Wm1 b,
    putK (putK t.2 Wm1 (stepLocK a W d)) Wm1 (stepLocK b W d))

/-- Walk a batch of divisor positions once, striking both windows. -/
@[expose] public noncomputable def treeFold2PairK (c lo Wm1 W start len : Nat) : Pair7 :=
  len.rec (zero7, zero7) fun i t =>
    (testBitK c i).rec t (treeDiv2PairK t lo Wm1 W (valueK (start.add i)))

/-! The definitions below repeat the tree with leaves of 262144 bits rather than 65536, so sixteen
leaves span the window where 128 did. `upd1` to `upd4` are unchanged, since a leaf's number and a
strike's offset within it do not mention the leaf's width; only the flatten steps and the split of
a strike into leaf and offset do. -/

/-- Two leaves of 262144 bits. -/
@[expose] public noncomputable def wflat1 (t : Lvl1) : Nat :=
  Nat.lor t.1 (Nat.shiftLeft t.2 262144)

/-- Four. -/
@[expose] public noncomputable def wflat2 (t : Lvl2) : Nat :=
  Nat.lor (wflat1 t.1) (Nat.shiftLeft (wflat1 t.2) 524288)

/-- Eight. -/
@[expose] public noncomputable def wflat3 (t : Lvl3) : Nat :=
  Nat.lor (wflat2 t.1) (Nat.shiftLeft (wflat2 t.2) 1048576)

/-- Sixteen, spanning a window of 4194304 bits. -/
@[expose] public noncomputable def wflat4 (t : Lvl4) : Nat :=
  Nat.lor (wflat3 t.1) (Nat.shiftLeft (wflat3 t.2) 2097152)

/-- Put one strike into a sixteen-leaf tree, or leave it alone where the strike passes the
window's end. -/
@[expose] public noncomputable def wputK (t : Lvl4) (Wm1 s : Nat) : Lvl4 :=
  (Nat.blt Wm1 s).rec (upd4 t (s.shiftRight 18) (s.land 262143)) t

/-- The two strikes of a divisor whose double already passes the window's end. -/
@[expose] public noncomputable def wtreeDiv2K (t : Lvl4) (lo Wm1 p : Nat) : Lvl4 :=
  let d : Nat := p.mul 2
  wputK (wputK t Wm1 (firstLocK (indexK (p.mul 5)) lo d)) Wm1
    (firstLocK (indexK (p.mul 7)) lo d)

/-- Walk the batch, two strikes to a divisor. -/
@[expose] public noncomputable def wtreeFold2K (c lo Wm1 start len : Nat) : Lvl4 :=
  len.rec zero4 fun i t =>
    (testBitK c i).rec t (wtreeDiv2K t lo Wm1 (valueK (start.add i)))

/-- The assembled mask of a batch, through leaves of 262144 bits. -/
@[expose] public noncomputable def wtreeBatch2K (c lo Wm1 start len : Nat) : Nat :=
  wflat4 (wtreeFold2K c lo Wm1 start len)

/-- The four strikes of a divisor whose double fits the window and whose quadruple does not. -/
@[expose] public noncomputable def wtreeDiv4K (t : Lvl4) (lo Wm1 p : Nat) : Lvl4 :=
  let d : Nat := p.mul 2
  let A : Nat := firstLocK (indexK (p.mul 5)) lo d
  let B : Nat := firstLocK (indexK (p.mul 7)) lo d
  wputK (wputK (wputK (wputK t Wm1 A) Wm1 B) Wm1 (A.add d)) Wm1 (B.add d)

/-- Walk the batch, four strikes to a divisor. -/
@[expose] public noncomputable def wtreeFold4K (c lo Wm1 start len : Nat) : Lvl4 :=
  len.rec zero4 fun i t =>
    (testBitK c i).rec t (wtreeDiv4K t lo Wm1 (valueK (start.add i)))

/-- The assembled mask of a four-strike batch, through leaves of 262144 bits. -/
@[expose] public noncomputable def wtreeBatch4K (c lo Wm1 start len : Nat) : Nat :=
  wflat4 (wtreeFold4K c lo Wm1 start len)

/-- The eight strikes of a divisor whose quadruple fits the window and whose octuple does not. -/
@[expose] public noncomputable def wtreeDivK (t : Lvl4) (lo Wm1 p : Nat) : Lvl4 :=
  let d : Nat := p.mul 2
  let A : Nat := firstLocK (indexK (p.mul 5)) lo d
  let B : Nat := firstLocK (indexK (p.mul 7)) lo d
  wputK (wputK (wputK (wputK (wputK (wputK (wputK (wputK t Wm1 A) Wm1 B)
    Wm1 (A.add d)) Wm1 (B.add d))
    Wm1 (A.add (p.mul 4))) Wm1 (B.add (p.mul 4)))
    Wm1 (A.add (d + p.mul 4))) Wm1 (B.add (d + p.mul 4))

/-- Walk the batch, eight strikes to a divisor. -/
@[expose] public noncomputable def wtreeFoldK (c lo Wm1 start len : Nat) : Lvl4 :=
  len.rec zero4 fun i t =>
    (testBitK c i).rec t (wtreeDivK t lo Wm1 (valueK (start.add i)))

/-- The assembled mask of an eight-strike batch, through leaves of 262144 bits. -/
@[expose] public noncomputable def wtreeBatchK (c lo Wm1 start len : Nat) : Nat :=
  wflat4 (wtreeFoldK c lo Wm1 start len)

/-! The same again with leaves of 1048576 bits, four of them spanning the window. -/

/-- Two leaves of 1048576 bits. -/
@[expose] public noncomputable def vflat1 (t : Lvl1) : Nat :=
  Nat.lor t.1 (Nat.shiftLeft t.2 1048576)

/-- Four, spanning a window of 4194304 bits. -/
@[expose] public noncomputable def vflat2 (t : Lvl2) : Nat :=
  Nat.lor (vflat1 t.1) (Nat.shiftLeft (vflat1 t.2) 2097152)

/-- Put one strike into a four-leaf tree, or leave it alone where the strike passes the window's
end. -/
@[expose] public noncomputable def vputK (t : Lvl2) (Wm1 s : Nat) : Lvl2 :=
  (Nat.blt Wm1 s).rec (upd2 t (s.shiftRight 20) (s.land 1048575)) t

/-- The two strikes of a divisor whose double already passes the window's end. -/
@[expose] public noncomputable def vtreeDiv2K (t : Lvl2) (lo Wm1 p : Nat) : Lvl2 :=
  let d : Nat := p.mul 2
  vputK (vputK t Wm1 (firstLocK (indexK (p.mul 5)) lo d)) Wm1
    (firstLocK (indexK (p.mul 7)) lo d)

/-- Walk the batch, two strikes to a divisor. -/
@[expose] public noncomputable def vtreeFold2K (c lo Wm1 start len : Nat) : Lvl2 :=
  len.rec zero2 fun i t =>
    (testBitK c i).rec t (vtreeDiv2K t lo Wm1 (valueK (start.add i)))

/-- The assembled mask of a batch, through leaves of 1048576 bits. -/
@[expose] public noncomputable def vtreeBatch2K (c lo Wm1 start len : Nat) : Nat :=
  vflat2 (vtreeFold2K c lo Wm1 start len)

/-- Four consecutive windows' trees. -/
@[expose] public noncomputable def Quad7 : Type := Pair7 × Pair7

/-- One divisor's two strikes in each of four consecutive windows, deriving the offsets for the
first window and stepping them three times. -/
@[expose] public noncomputable def treeDiv2QuadK (t : Quad7) (lo Wm1 W p : Nat) : Quad7 :=
  let d : Nat := p.mul 2
  let a0 : Nat := firstLocK (indexK (p.mul 5)) lo d
  let b0 : Nat := firstLocK (indexK (p.mul 7)) lo d
  let a1 : Nat := stepLocK a0 W d
  let b1 : Nat := stepLocK b0 W d
  let a2 : Nat := stepLocK a1 W d
  let b2 : Nat := stepLocK b1 W d
  ((putK (putK t.1.1 Wm1 a0) Wm1 b0, putK (putK t.1.2 Wm1 a1) Wm1 b1),
    (putK (putK t.2.1 Wm1 a2) Wm1 b2,
      putK (putK t.2.2 Wm1 (stepLocK a2 W d)) Wm1 (stepLocK b2 W d)))

/-- Walk a batch of divisor positions once, striking four windows. -/
@[expose] public noncomputable def treeFold2QuadK (c lo Wm1 W start len : Nat) : Quad7 :=
  len.rec ((zero7, zero7), (zero7, zero7)) fun i t =>
    (testBitK c i).rec t (treeDiv2QuadK t lo Wm1 W (valueK (start.add i)))

/-- All four windows' assembled masks from one walk, as one number, window `j` occupying bits
`j * W` to `j * W + W - 1`. One equation settles all four. -/
@[expose] public noncomputable def treeBatchQuad2K (c lo Wm1 W start len : Nat) : Nat :=
  let t : Quad7 := treeFold2QuadK c lo Wm1 W start len
  Nat.lor (Nat.lor (flat7 t.1.1) (Nat.shiftLeft (flat7 t.1.2) W))
    (Nat.lor (Nat.shiftLeft (flat7 t.2.1) (W.mul 2))
      (Nat.shiftLeft (flat7 t.2.2) (W.mul 3)))

/-- Both windows' assembled masks from one walk of the batch, as one number: the first window in
bits `0` to `W - 1` and the second in bits `W` upwards. One equation settles both. -/
@[expose] public noncomputable def treeBatchPair2K (c lo Wm1 W start len : Nat) : Nat :=
  let t : Pair7 := treeFold2PairK c lo Wm1 W start len
  Nat.lor (flat7 t.1) (Nat.shiftLeft (flat7 t.2) W)

/-! The four definitions below exist only so that the seed offset's two forms can be timed against
each other inside one file, under a real batch. They carry no proofs: mode 46 settles both by
`reflBoolTrue` and reports them apart. -/

/-- The seed offset as it was written before, through the quotient. -/
@[expose] public def firstLocOldK (A lo m : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add A (Nat.mul m (Nat.succ (Nat.div lo m)))) lo) m

/-- `treeDiv2K` through the old seed offset. -/
@[expose] public noncomputable def treeDiv2OldK (t : Lvl7) (lo Wm1 p : Nat) : Lvl7 :=
  let d : Nat := p.mul 2
  putK (putK t Wm1 (firstLocOldK (indexK (p.mul 5)) lo d)) Wm1
    (firstLocOldK (indexK (p.mul 7)) lo d)

/-- `treeFold2K` through the old seed offset. -/
@[expose] public noncomputable def treeFold2OldK (c lo Wm1 start len : Nat) : Lvl7 :=
  len.rec zero7 fun i t =>
    (testBitK c i).rec t (treeDiv2OldK t lo Wm1 (valueK (start.add i)))

/-- `treeBatch2K` through the old seed offset. -/
@[expose] public noncomputable def treeBatch2OldK (c lo Wm1 start len : Nat) : Nat :=
  flat7 (treeFold2OldK c lo Wm1 start len)

/-- The four strikes of a divisor whose double fits the window and whose quadruple does not. -/
@[expose] public noncomputable def treeDiv4K (t : Lvl7) (lo Wm1 p : Nat) : Lvl7 :=
  let d : Nat := p.mul 2
  let A : Nat := firstLocK (indexK (p.mul 5)) lo d
  let B : Nat := firstLocK (indexK (p.mul 7)) lo d
  putK (putK (putK (putK t Wm1 A) Wm1 B) Wm1 (A.add d)) Wm1 (B.add d)

/-- Walk the batch, four strikes to a divisor. -/
@[expose] public noncomputable def treeFold4K (c lo Wm1 start len : Nat) : Lvl7 :=
  len.rec zero7 fun i t =>
    (testBitK c i).rec t (treeDiv4K t lo Wm1 (valueK (start.add i)))

/-- The assembled mask of a batch whose divisors strike three or four times. -/
@[expose] public noncomputable def treeBatch4K (c lo Wm1 start len : Nat) : Nat :=
  flat7 (treeFold4K c lo Wm1 start len)

/-! ### The same design at half the slice width

Every entry of a batch joins two bits into the state of the slice it lands in, and there are tens
of thousands of entries to a batch against sixty-five slices. Rewriting `stripeSort` taught that
what such a loop costs follows the width of the number being joined into rather than the number of
bits set in it, and the slice width is the one dimension of this design that has never been swept.
Halving it to 32768 was measured and lost, 2.8 and 3.6 percent of kernel and 6.3 of peak, so these
definitions now carry 131072-bit slices instead, 32 to a batch rather than 64. Timing only, and no
proofs: if it wins the proofs are the same ones with a different constant. -/

/-- `entryTallyK` with the tally starting above a 131072-bit slice. -/
@[expose] public noncomputable def entryTallyS (len e : Nat) : Nat :=
  Nat.add 131072 (Nat.add (e.shiftRight 3) (Nat.mul (e.land 7) len))

/-- `stripeEntryK` over 131072-bit slices, so a seed's slice is its top bits above 17. -/
@[expose] public noncomputable def stripeEntryS (st c lo start k len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 3)).rec st
    ((Nat.beq ((entrySeedK lo start e).shiftRight 17) k).rec st
      (st.lor ((Nat.shiftLeft 1 ((entrySeedK lo start e).land 131071)).lor
        (Nat.shiftLeft 1 (entryTallyS len e)))))

/-- `stripeOutK` over 131072-bit slices. -/
@[expose] public noncomputable def stripeOutS (st c lo start Wm1 len e : Nat) : Nat :=
  (testBitK c (e.shiftRight 3)).rec st
    ((Nat.blt Wm1 (entrySeedK lo start e)).rec st
      (st.lor (Nat.shiftLeft 1 (entryTallyS len e))))

/-- The entries of one 131072-bit slice's list. -/
@[expose] public noncomputable def stripeSlotS (c lo start k len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeEntryS s c lo start k len ((slot.shiftRight (j.mul 16)).land 65535)

/-- The entries of the out-of-window list, over 131072-bit slices. -/
@[expose] public noncomputable def stripeOutSlotS (c lo start Wm1 len slot cnt st : Nat) : Nat :=
  cnt.rec st fun j s =>
    stripeOutS s c lo start Wm1 len ((slot.shiftRight (j.mul 16)).land 65535)

/-- `stripeUpToK` over 131072-bit slices. -/
@[expose] public noncomputable def stripeUpToS
    (c lo start len W Wm1 slotW Ls Cs np n : Nat) : Nat :=
  n.rec 0 fun k asm =>
    let slot : Nat := (Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)
    let cnt : Nat := (Cs.shiftRight (k.mul 16)).land 65535
    let st : Nat := (Nat.beq k np).rec
      (stripeSlotS c lo start k len slot cnt 0)
      (stripeOutSlotS c lo start Wm1 len slot cnt 0)
    (asm.lor ((st.land (Nat.sub (Nat.shiftLeft 1 131072) 1)).shiftLeft (k.mul 131072))).lor
      ((st.shiftRight 131072).shiftLeft W)

/-- The same assembled number as `stripeBatchK`, built from twice as many slices of half the
width. -/
@[expose] public noncomputable def stripeBatchS
    (c lo start len W Wm1 slotW Ls Cs np : Nat) : Nat :=
  stripeUpToS c lo start len W Wm1 slotW Ls Cs np (np + 1)

/-- The state a slice's list is walked from, and what it contributes to the assembled number. -/
@[expose] public noncomputable def stripeStateK (c lo start len Wm1 slotW Ls Cs np k : Nat) : Nat :=
  (Nat.beq k np).rec
    (stripeSlotK c lo start k len
      ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
      ((Cs.shiftRight (k.mul 16)).land 65535) 0)
    (stripeOutSlotK c lo start Wm1 len
      ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
      ((Cs.shiftRight (k.mul 16)).land 65535) 0)

/-! ### Joining the slices in pairs rather than one into a window-wide accumulator

`stripeUpToK` shifts each finished slice into its place in a number that is already as wide as the
window, and joins the tally into the same number, so every slice touches the full width twice.
`joinJK` below joins the slices in pairs instead, doubling the width as it goes, and the tally is
accumulated apart and joined once at the end. Prototype: no soundness is proved, and the kernel
checks the literal, which is what a timing pair needs. -/

/-- The leaves `k` through `k + 2 ^ d - 1` joined in pairs, each leaf `w` bits wide. The recursion
is on the depth and returns a function, so the index arrives after the branch is chosen. -/
@[expose] public noncomputable def joinJK (leaf : Nat → Nat) (w : Nat) : Nat → Nat → Nat :=
  fun d => Nat.rec (motive := fun _ => Nat → Nat) leaf
    (fun i ih k => (ih k).lor ((ih (k.add (Nat.shiftLeft 1 i))).shiftLeft (Nat.shiftLeft w i))) d

/-- The tallies of every slice, joined as a number no wider than the tally itself. -/
@[expose] public noncomputable def stripeTallyJK
    (c lo start len Wm1 slotW Ls Cs np n : Nat) : Nat :=
  n.rec 0 fun k t =>
    t.lor ((stripeStateK c lo start len Wm1 slotW Ls Cs np k).shiftRight 65536)

/-- The same assembled number as `stripeBatchK`, with the window's slices joined in pairs and the
tally carried separately. `d` is the depth, so the window holds `2 ^ d` slices. -/
@[expose] public noncomputable def stripeBatchJK
    (c lo start len W Wm1 slotW Ls Cs np d : Nat) : Nat :=
  (joinJK (fun k =>
      (stripeStateK c lo start len Wm1 slotW Ls Cs np k).land
        (Nat.sub (Nat.shiftLeft 1 65536) 1)) 65536 d 0).lor
    ((stripeTallyJK c lo start len Wm1 slotW Ls Cs np (np + 1)).shiftLeft W)

/-- One more slice. -/
public theorem stripeUpToK_succ {c lo start len W Wm1 slotW Ls Cs np n : Nat} :
    stripeUpToK c lo start len W Wm1 slotW Ls Cs np (n + 1)
      = ((stripeUpToK c lo start len W Wm1 slotW Ls Cs np n).lor
          (((stripeStateK c lo start len Wm1 slotW Ls Cs np n).land
            (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (n.mul 65536))).lor
        (((stripeStateK c lo start len Wm1 slotW Ls Cs np n).shiftRight 65536).shiftLeft W) := rfl

/-! ### What one entry does

Each step of either fold leaves the state alone or joins two single bits into it, so a bit of the
result is a bit of the state unless it is one of those two. These two lemmas are the base of the
induction over a slice's list. -/

/-- A single bit, tested. -/
public theorem testBit_oneShift {a b : Nat} : (Nat.shiftLeft 1 a).testBit b = Nat.beq b a := by
  have hs : Nat.shiftLeft 1 a = 1 <<< a := rfl
  have h : (1 : Nat) <<< a = 2 ^ a := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hs, h, Nat.testBit_two_pow]
  cases hb : Nat.beq b a with
  | true => simp [Nat.eq_of_beq_eq_true hb]
  | false =>
    have hne : a ≠ b := by
      intro hba
      rw [← hba] at hb
      simp at hb
    simp [hne]

/-- Whether the entry `e` of slice `k`'s list sets bit `j`: it does when the batch holds a prime at
the position `e` names, that prime's seed lands in slice `k`, and `j` is either that seed's place in
the slice or the entry's place in the tally. -/
@[expose] public noncomputable def entryHits (c lo start k len j e : Nat) : Bool :=
  testBitK c (e.shiftRight 3) && Nat.beq ((entrySeedK lo start e).shiftRight 16) k &&
    (Nat.beq j ((entrySeedK lo start e).land 65535) || Nat.beq j (entryTallyK len e))

/-- The same for the out-of-window list, where only the tally bit is set. -/
@[expose] public noncomputable def outHits (c lo start Wm1 len j e : Nat) : Bool :=
  testBitK c (e.shiftRight 3) && Nat.blt Wm1 (entrySeedK lo start e) &&
    Nat.beq j (entryTallyK len e)

/-- A step of a slice's list, one bit at a time. -/
public theorem testBit_stripeEntryK {st c lo start k len e j : Nat} :
    (stripeEntryK st c lo start k len e).testBit j
      = (st.testBit j || entryHits c lo start k len j e) := by
  unfold entryHits
  unfold stripeEntryK
  cases hc : testBitK c (e.shiftRight 3) with
  | false => simp
  | true =>
    cases hk : Nat.beq ((entrySeedK lo start e).shiftRight 16) k with
    | false => simp
    | true =>
      have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
      rw [hlor, hlor, Nat.testBit_or, Nat.testBit_or, testBit_oneShift, testBit_oneShift]
      simp

/-- A step of the out-of-window list, one bit at a time. -/
public theorem testBit_stripeOutK {st c lo start Wm1 len e j : Nat} :
    (stripeOutK st c lo start Wm1 len e).testBit j
      = (st.testBit j || outHits c lo start Wm1 len j e) := by
  unfold outHits
  unfold stripeOutK
  cases hc : testBitK c (e.shiftRight 3) with
  | false => simp
  | true =>
    cases hw : Nat.blt Wm1 (entrySeedK lo start e) with
    | false => simp
    | true =>
      have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
      rw [hlor, Nat.testBit_or, testBit_oneShift]
      simp

/-- Walking one more entry. -/
public theorem stripeSlotK_succ {c lo start k len slot cnt st : Nat} :
    stripeSlotK c lo start k len slot (cnt + 1) st
      = stripeEntryK (stripeSlotK c lo start k len slot cnt st) c lo start k len
          ((slot.shiftRight (cnt.mul 16)).land 65535) := rfl

/-- Walking one more entry of the out-of-window list. -/
public theorem stripeOutSlotK_succ {c lo start Wm1 len slot cnt st : Nat} :
    stripeOutSlotK c lo start Wm1 len slot (cnt + 1) st
      = stripeOutK (stripeOutSlotK c lo start Wm1 len slot cnt st) c lo start Wm1 len
          ((slot.shiftRight (cnt.mul 16)).land 65535) := rfl

/-- A bit of a finished list is a bit of what the walk started from, or one that some entry of the
list set. -/
public theorem testBit_stripeSlotK {c lo start k len slot st j : Nat} (cnt : Nat) :
    (stripeSlotK c lo start k len slot cnt st).testBit j = true ↔
      (st.testBit j = true ∨ ∃ m, m < cnt ∧
        entryHits c lo start k len j ((slot.shiftRight (m.mul 16)).land 65535) = true) := by
  induction cnt with
  | zero =>
    have h : stripeSlotK c lo start k len slot 0 st = st := rfl
    rw [h]
    constructor
    · exact fun hj => Or.inl hj
    · rintro (hj | ⟨m, hm, _⟩)
      · exact hj
      · exact absurd hm (by lia)
  | succ n ih =>
    rw [stripeSlotK_succ, testBit_stripeEntryK, Bool.or_eq_true, ih]
    constructor
    · rintro ((hj | ⟨m, hm, he⟩) | hn)
      · exact Or.inl hj
      · exact Or.inr ⟨m, by lia, he⟩
      · exact Or.inr ⟨n, by lia, hn⟩
    · rintro (hj | ⟨m, hm, he⟩)
      · exact Or.inl (Or.inl hj)
      · rcases Nat.lt_or_ge m n with hmn | hmn
        · exact Or.inl (Or.inr ⟨m, hmn, he⟩)
        · have : m = n := by lia
          rw [this] at he
          exact Or.inr he

/-- The same for the out-of-window list. -/
public theorem testBit_stripeOutSlotK {c lo start Wm1 len slot st j : Nat} (cnt : Nat) :
    (stripeOutSlotK c lo start Wm1 len slot cnt st).testBit j = true ↔
      (st.testBit j = true ∨ ∃ m, m < cnt ∧
        outHits c lo start Wm1 len j ((slot.shiftRight (m.mul 16)).land 65535) = true) := by
  induction cnt with
  | zero =>
    have h : stripeOutSlotK c lo start Wm1 len slot 0 st = st := rfl
    rw [h]
    constructor
    · exact fun hj => Or.inl hj
    · rintro (hj | ⟨m, hm, _⟩)
      · exact hj
      · exact absurd hm (by lia)
  | succ n ih =>
    rw [stripeOutSlotK_succ, testBit_stripeOutK, Bool.or_eq_true, ih]
    constructor
    · rintro ((hj | ⟨m, hm, he⟩) | hn)
      · exact Or.inl hj
      · exact Or.inr ⟨m, by lia, he⟩
      · exact Or.inr ⟨n, by lia, hn⟩
    · rintro (hj | ⟨m, hm, he⟩)
      · exact Or.inl (Or.inl hj)
      · rcases Nat.lt_or_ge m n with hmn | hmn
        · exact Or.inl (Or.inr ⟨m, hmn, he⟩)
        · have : m = n := by lia
          rw [this] at he
          exact Or.inr he

/-- Keeping the low `n` bits. -/
public theorem testBit_maskLow {x b n : Nat} :
    (x.land (Nat.sub (Nat.shiftLeft 1 n) 1)).testBit b = (x.testBit b && decide (b < n)) := by
  have hl : x.land (Nat.sub (Nat.shiftLeft 1 n) 1) = x &&& (Nat.sub (Nat.shiftLeft 1 n) 1) := rfl
  have hs : Nat.shiftLeft 1 n = 1 <<< n := rfl
  have h : (1 : Nat) <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hsub : Nat.sub (2 ^ n) 1 = 2 ^ n - 1 := rfl
  rw [hl, hs, h, hsub, Nat.testBit_and, Nat.testBit_two_pow_sub_one]

/-- Moving a number up. -/
public theorem testBit_shiftUp {x b s : Nat} :
    (x.shiftLeft s).testBit b = (decide (s ≤ b) && x.testBit (b - s)) := by
  have hs : x.shiftLeft s = x <<< s := rfl
  rw [hs, Nat.testBit_shiftLeft]

/-- The list of seeds past the end of the window sets only tally bits, so it contributes nothing to
the window itself. -/
public theorem stripeOutSlotK_low {c lo start Wm1 len slot cnt b : Nat} (hb : b < 65536) :
    (stripeOutSlotK c lo start Wm1 len slot cnt 0).testBit b = false := by
  rcases Bool.eq_false_or_eq_true
    ((stripeOutSlotK c lo start Wm1 len slot cnt 0).testBit b) with h | h
  · rcases (testBit_stripeOutSlotK cnt).mp h with hz | ⟨m, _, he⟩
    · simp at hz
    · unfold outHits at he
      have hj := (Bool.and_eq_true ..).mp he
      have hbeq : b = entryTallyK len ((slot.shiftRight (m.mul 16)).land 65535) :=
        Nat.eq_of_beq_eq_true hj.2
      have hge : 65536 ≤ entryTallyK len ((slot.shiftRight (m.mul 16)).land 65535) := by
        unfold entryTallyK
        lia
      exact absurd hbeq (by lia)
  · exact h

/-- Below the window's width, a bit of the assembled number comes from exactly one slice: the one
its position falls in. -/
public theorem testBit_stripeUpToK_low {c lo start len W Wm1 slotW Ls Cs np j : Nat} (hj : j < W)
    (n : Nat) :
    (stripeUpToK c lo start len W Wm1 slotW Ls Cs np n).testBit j = true ↔
      ∃ k, k < n ∧ k * 65536 ≤ j ∧ j - k * 65536 < 65536 ∧
        (stripeStateK c lo start len Wm1 slotW Ls Cs np k).testBit (j - k * 65536) = true := by
  induction n with
  | zero =>
    have h : stripeUpToK c lo start len W Wm1 slotW Ls Cs np 0 = 0 := rfl
    rw [h]
    constructor
    · intro hb
      simp at hb
    · rintro ⟨k, hk, _⟩
      exact absurd hk (by lia)
  | succ m ih =>
    have hlor : ∀ u v : Nat, u.lor v = u ||| v := fun _ _ => rfl
    rw [stripeUpToK_succ, hlor, hlor, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true,
      Bool.or_eq_true, ih]
    have hhigh : (((stripeStateK c lo start len Wm1 slotW Ls Cs np m).shiftRight 65536).shiftLeft
        W).testBit j = false := by
      rw [testBit_shiftUp]
      have : ¬ W ≤ j := by lia
      simp [this]
    have hmid : (((stripeStateK c lo start len Wm1 slotW Ls Cs np m).land
        (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (m.mul 65536)).testBit j
        = (decide (m * 65536 ≤ j) &&
            ((stripeStateK c lo start len Wm1 slotW Ls Cs np m).testBit (j - m * 65536) &&
              decide (j - m * 65536 < 65536))) := by
      have hm : m.mul 65536 = m * 65536 := rfl
      rw [testBit_shiftUp, hm, testBit_maskLow]
    rw [hhigh, hmid]
    constructor
    · rintro ((⟨k, hk, h1, h2, h3⟩ | hmid') | hfalse)
      · exact ⟨k, by lia, h1, h2, h3⟩
      · have h := Bool.and_eq_true .. |>.mp hmid'
        have h' := Bool.and_eq_true .. |>.mp h.2
        exact ⟨m, by lia, by simpa using h.1, by simpa using h'.2, h'.1⟩
      · simp at hfalse
    · rintro ⟨k, hk, h1, h2, h3⟩
      rcases Nat.lt_or_ge k m with hkm | hkm
      · exact Or.inl (Or.inl ⟨k, hkm, h1, h2, h3⟩)
      · have hkeq : k = m := by lia
        rw [hkeq] at h1 h2 h3
        refine Or.inl (Or.inr ?_)
        simp [h1, h2, h3]

/-- At or above the window's width, a bit of the assembled number is one of the tally bits, and any
slice can have contributed it. -/
public theorem testBit_stripeUpToK_high {c lo start len W Wm1 slotW Ls Cs np j : Nat} (hj : W ≤ j)
    (hW : np * 65536 ≤ W) (n : Nat) (hn : n ≤ np + 1) :
    (stripeUpToK c lo start len W Wm1 slotW Ls Cs np n).testBit j = true ↔
      ∃ k, k < n ∧
        (stripeStateK c lo start len Wm1 slotW Ls Cs np k).testBit (65536 + (j - W)) = true := by
  induction n with
  | zero =>
    have h : stripeUpToK c lo start len W Wm1 slotW Ls Cs np 0 = 0 := rfl
    rw [h]
    constructor
    · intro hb
      simp at hb
    · rintro ⟨k, hk, _⟩
      exact absurd hk (by lia)
  | succ m ih =>
    have hlor : ∀ u v : Nat, u.lor v = u ||| v := fun _ _ => rfl
    rw [stripeUpToK_succ, hlor, hlor, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true,
      Bool.or_eq_true, ih (by lia)]
    have hmid : (((stripeStateK c lo start len Wm1 slotW Ls Cs np m).land
        (Nat.sub (Nat.shiftLeft 1 65536) 1)).shiftLeft (m.mul 65536)).testBit j = false := by
      have hm : m.mul 65536 = m * 65536 := rfl
      rw [testBit_shiftUp, hm, testBit_maskLow]
      rcases Nat.lt_or_ge m np with hlt | hge
      · have : ¬ (j - m * 65536 < 65536) := by
          have h1 : (m + 1) * 65536 ≤ np * 65536 := Nat.mul_le_mul_right 65536 (by lia)
          lia
        simp [this]
      · have hm64 : m = np := by lia
        rw [hm64]
        rcases Nat.lt_or_ge (j - np * 65536) 65536 with hb | hb
        · have hst : (stripeStateK c lo start len Wm1 slotW Ls Cs np np).testBit
              (j - np * 65536) = false := by
            have hdef : stripeStateK c lo start len Wm1 slotW Ls Cs np np
                = stripeOutSlotK c lo start Wm1 len
                  ((Ls.shiftRight (slotW.mul np)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
                  ((Cs.shiftRight (np.mul 16)).land 65535) 0 := by
              have hbeq : Nat.beq np np = true := Nat.beq_eq.mpr rfl
              unfold stripeStateK
              rw [hbeq]
            rw [hdef]
            exact stripeOutSlotK_low hb
          simp [hst]
        · simp [Nat.not_lt_of_ge hb]
    have hhigh : (((stripeStateK c lo start len Wm1 slotW Ls Cs np m).shiftRight 65536).shiftLeft
        W).testBit j
        = (stripeStateK c lo start len Wm1 slotW Ls Cs np m).testBit (65536 + (j - W)) := by
      have hsr : ∀ u v b : Nat, (u.shiftRight v).testBit b = u.testBit (v + b) := by
        intro u v b
        have h : u.shiftRight v = u >>> v := rfl
        rw [h, Nat.testBit_shiftRight]
      rw [testBit_shiftUp, hsr]
      simp [hj]
    rw [hmid, hhigh]
    constructor
    · rintro ((⟨k, hk, h3⟩ | hf) | hlast)
      · exact ⟨k, by lia, h3⟩
      · simp at hf
      · exact ⟨m, by lia, hlast⟩
    · rintro ⟨k, hk, h3⟩
      rcases Nat.lt_or_ge k m with hkm | hkm
      · exact Or.inl (Or.inl ⟨k, hkm, h3⟩)
      · have hkeq : k = m := by lia
        rw [hkeq] at h3
        exact Or.inr h3

/-- Entry `m` of slice `k`'s list. -/
@[expose] public noncomputable def entryOf (Ls slotW k m : Nat) : Nat :=
  ((((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)).shiftRight
    (m.mul 16)).land 65535)

/-- How many entries slice `k`'s list holds. -/
@[expose] public noncomputable def cntOf (Cs k : Nat) : Nat :=
  (Cs.shiftRight (k.mul 16)).land 65535

/-- Dividing by the slice width, two ways. -/
public theorem shiftRight16_eq {x : Nat} : x.shiftRight 16 = x / 65536 := by
  have h : x.shiftRight 16 = x >>> 16 := rfl
  have h2 : (2 : Nat) ^ 16 = 65536 := rfl
  rw [h, Nat.shiftRight_eq_div_pow, h2]

/-- The offset within a slice, two ways. -/
public theorem land65535_eq {x : Nat} : x.land 65535 = x % 65536 := by
  have h : x.land 65535 = x &&& (2 ^ 16 - 1) := rfl
  have h2 : (2 : Nat) ^ 16 = 65536 := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod, h2]

/-- The entry an index names, as the walk over a list sees it. -/
public theorem entryOf_eq {Ls slotW k m : Nat} :
    entryOf Ls slotW k m
      = ((((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1)).shiftRight
          (m.mul 16)).land 65535) := rfl

/-- A number is equal to itself. -/
public theorem beq_self {x : Nat} : Nat.beq x x = true := Nat.beq_eq.mpr rfl

/-- Two different numbers are not equal. -/
public theorem beq_of_ne {x y : Nat} (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y with
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
  | false => rfl

/-- An entry that writes into its slice writes its own bit into the tally as well, which is how a
finished batch says which strikes it accounted for. -/
public theorem testBit_stripeBatchK_tally {c lo start len W Wm1 slotW Ls Cs np k m : Nat}
    (hW : np * 65536 ≤ W) (hk : k < np) (hm : m < cntOf Cs k)
    (hc : testBitK c ((entryOf Ls slotW k m).shiftRight 3) = true)
    (hk16 : (entrySeedK lo start (entryOf Ls slotW k m)).shiftRight 16 = k) :
    (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit
      (W + ((entryOf Ls slotW k m).shiftRight 3
        + (entryOf Ls slotW k m).land 7 * len)) = true := by
  have hbatch : stripeBatchK c lo start len W Wm1 slotW Ls Cs np
      = stripeUpToK c lo start len W Wm1 slotW Ls Cs np (np + 1) := rfl
  rw [hbatch]
  refine (testBit_stripeUpToK_high (by lia :
    W ≤ W + ((entryOf Ls slotW k m).shiftRight 3
      + (entryOf Ls slotW k m).land 7 * len)) hW (np + 1) (by lia)).mpr ⟨k, by lia, ?_⟩
  have hJ : 65536 + (W + ((entryOf Ls slotW k m).shiftRight 3
      + (entryOf Ls slotW k m).land 7 * len) - W)
      = 65536 + ((entryOf Ls slotW k m).shiftRight 3
        + (entryOf Ls slotW k m).land 7 * len) := by lia
  rw [hJ]
  have hstate : stripeStateK c lo start len Wm1 slotW Ls Cs np k
      = stripeSlotK c lo start k len
        ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
        (cntOf Cs k) 0 := by
    unfold stripeStateK cntOf
    rw [beq_of_ne (by lia : k ≠ np)]
  rw [hstate]
  refine (testBit_stripeSlotK (cntOf Cs k)).mpr (Or.inr ⟨m, hm, ?_⟩)
  unfold entryHits
  exact (Bool.and_eq_true ..).mpr ⟨(Bool.and_eq_true ..).mpr ⟨hc, Nat.beq_eq.mpr hk16⟩,
    (Bool.or_eq_true ..).mpr (Or.inr beq_self)⟩

/-- A position of the window is set in the assembled number exactly when some entry, recorded in
the slice that position falls in, names a prime of the batch whose seed is that position. -/
public theorem testBit_stripeBatchK_eq {c lo start len W Wm1 slotW Ls Cs np j : Nat} (hj : j < W) :
    (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit j = true ↔
      ∃ k m, k < np ∧ m < cntOf Cs k ∧
        testBitK c ((entryOf Ls slotW k m).shiftRight 3) = true ∧
        (entrySeedK lo start (entryOf Ls slotW k m)).shiftRight 16 = k ∧
        entrySeedK lo start (entryOf Ls slotW k m) = j := by
  have hbatch : stripeBatchK c lo start len W Wm1 slotW Ls Cs np
      = stripeUpToK c lo start len W Wm1 slotW Ls Cs np (np + 1) := rfl
  rw [hbatch, testBit_stripeUpToK_low hj (np + 1)]
  constructor
  · rintro ⟨k, hk65, hkle, hklt, hst⟩
    rcases Nat.lt_or_ge k np with hk | hk
    · have hstate : stripeStateK c lo start len Wm1 slotW Ls Cs np k
          = stripeSlotK c lo start k len
            ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
            (cntOf Cs k) 0 := by
        unfold stripeStateK cntOf
        rw [beq_of_ne (by lia : k ≠ np)]
      rw [hstate] at hst
      rcases (testBit_stripeSlotK (cntOf Cs k)).mp hst with hz | ⟨m, hm, he⟩
      · simp at hz
      · unfold entryHits at he
        have h1 := (Bool.and_eq_true ..).mp he
        have h2 := (Bool.and_eq_true ..).mp h1.1
        have hk16 : (entrySeedK lo start (entryOf Ls slotW k m)).shiftRight 16 = k :=
          Nat.eq_of_beq_eq_true h2.2
        refine ⟨k, m, hk, hm, h2.1, hk16, ?_⟩
        rcases (Bool.or_eq_true ..).mp h1.2 with hseed | htally
        · have hlow : j - k * 65536
              = (entrySeedK lo start (entryOf Ls slotW k m)).land 65535 :=
            Nat.eq_of_beq_eq_true hseed
          rw [shiftRight16_eq] at hk16
          rw [land65535_eq] at hlow
          have := Nat.div_add_mod (entrySeedK lo start (entryOf Ls slotW k m)) 65536
          lia
        · have hte : j - k * 65536 = entryTallyK len (entryOf Ls slotW k m) :=
            Nat.eq_of_beq_eq_true htally
          have hge : 65536 ≤ entryTallyK len (entryOf Ls slotW k m) := by
            unfold entryTallyK
            lia
          exact absurd hte (by lia)
    · have hk64 : k = np := by lia
      rw [hk64] at hst
      have hstate : stripeStateK c lo start len Wm1 slotW Ls Cs np np
          = stripeOutSlotK c lo start Wm1 len
            ((Ls.shiftRight (slotW.mul np)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
            (cntOf Cs np) 0 := by
        have hbeq : Nat.beq np np = true := Nat.beq_eq.mpr rfl
        unfold stripeStateK cntOf
        rw [hbeq]
      rw [hstate] at hst
      rw [stripeOutSlotK_low (by lia)] at hst
      simp at hst
  · rintro ⟨k, m, hk, hm, hc, hk16, hseed⟩
    rw [shiftRight16_eq] at hk16
    have hdm := Nat.div_add_mod (entrySeedK lo start (entryOf Ls slotW k m)) 65536
    have hmod : entrySeedK lo start (entryOf Ls slotW k m) % 65536 < 65536 :=
      Nat.mod_lt _ (by lia)
    refine ⟨k, by lia, by lia, by lia, ?_⟩
    have hstate : stripeStateK c lo start len Wm1 slotW Ls Cs np k
        = stripeSlotK c lo start k len
          ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
          (cntOf Cs k) 0 := by
      unfold stripeStateK cntOf
      rw [beq_of_ne (by lia : k ≠ np)]
    rw [hstate]
    refine (testBit_stripeSlotK (cntOf Cs k)).mpr (Or.inr ⟨m, hm, ?_⟩)
    unfold entryHits
    have hlow : j - k * 65536 = (entrySeedK lo start (entryOf Ls slotW k m)).land 65535 := by
      rw [land65535_eq]
      lia
    have hbeq : Nat.beq (j - k * 65536)
        ((entrySeedK lo start (entryOf Ls slotW k m)).land 65535) = true := by
      rw [hlow]
      exact beq_self
    have hk16' : Nat.beq ((entrySeedK lo start (entryOf Ls slotW k m)).shiftRight 16) k = true := by
      rw [shiftRight16_eq, hk16]
      exact beq_self
    rw [← entryOf_eq, hc, hk16', hbeq]
    simp

/-- A batch's slice of the base sieve holds `len` bits, so it says nothing at a position outside
the batch, which is what stops an entry naming such a position from forging a tally bit. -/
public theorem testBitK_of_lt {c len i : Nat} (hc : c < 2 ^ len) (hi : len ≤ i) :
    testBitK c i = false := by
  rw [testBitK_eq_testBit]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by lia) hi))

/-- A tally bit names one position of the batch and one of a divisor's four possible strikes. -/
public theorem entryTallyK_inj {len e i w : Nat} (hi : (e.shiftRight 3) < len) (hi' : i < len)
    (h : entryTallyK len e = Nat.add 65536 (Nat.add i (Nat.mul w len))) :
    e.shiftRight 3 = i ∧ e.land 7 = w := by
  unfold entryTallyK at h
  have hlen : 0 < len := by lia
  have hadd : e.shiftRight 3 + (e.land 7) * len = i + w * len := by lia
  have hmod : (e.shiftRight 3 + (e.land 7) * len) % len = (i + w * len) % len := by rw [hadd]
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hi'] at hmod
  refine ⟨hmod, ?_⟩
  have hmul : (e.land 7) * len = w * len := by lia
  exact Nat.eq_of_mul_eq_mul_right hlen hmul

/-! ### The record decode, for any lane width

The six lemmas after these bake in a three-bit lane. A band wanting sixteen lanes needs four bits,
and these are the same facts with the width left open: div and mod, which generalise without
effort. Having them is what makes a wider band affordable, since the proofs above the decode reach
it only through these. -/

public theorem shiftRightLw_eq {e lw : Nat} : e.shiftRight lw = e / 2 ^ lw := by
  have h : e.shiftRight lw = e >>> lw := rfl
  rw [h, Nat.shiftRight_eq_div_pow]

public theorem landLw_eq {e lw : Nat} : e.land (2 ^ lw - 1) = e % 2 ^ lw := by
  have h : e.land (2 ^ lw - 1) = e &&& (2 ^ lw - 1) := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

/-- An entry is its position and which strike it names, at any lane width. -/
public theorem entry_splitLw {e lw : Nat} :
    2 ^ lw * (e.shiftRight lw) + e.land (2 ^ lw - 1) = e := by
  rw [shiftRightLw_eq, landLw_eq]
  have := Nat.div_add_mod e (2 ^ lw)
  lia

/-- A strike is one of `2 ^ lw`. -/
public theorem landLw_lt {e lw : Nat} : e.land (2 ^ lw - 1) < 2 ^ lw := by
  rw [landLw_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos lw)

/-- The position an assembled entry names, at any lane width. -/
public theorem shiftRightLw_pair {i w lw : Nat} (hw : w < 2 ^ lw) :
    (2 ^ lw * i + w).shiftRight lw = i := by
  rw [shiftRightLw_eq, Nat.mul_add_div (Nat.two_pow_pos lw), Nat.div_eq_of_lt hw, Nat.add_zero]

/-- The strike an assembled entry names, at any lane width. -/
public theorem landLw_pair {i w lw : Nat} (hw : w < 2 ^ lw) :
    (2 ^ lw * i + w).land (2 ^ lw - 1) = w := by
  rw [landLw_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hw]

/-- The lane mask, as the decode lemmas write it. `Nat.shiftLeft 1 lw` only reduces to `2 ^ lw`
when `lw` is a literal, so with the width open the two forms need connecting. -/
public theorem laneMaskK_eq {lw : Nat} : laneMaskK lw = 2 ^ lw - 1 := by
  unfold laneMaskK
  have h : Nat.shiftLeft 1 lw = 1 <<< lw := rfl
  rw [h, Nat.shiftLeft_eq, Nat.one_mul]
  rfl

/-- Which strike a record names, at any lane width. The three-bit `entrySeedK_pair` is bounded at
`w < 8`, and the eight named lane lemmas after it are that one at `w = 0 … 7`. With the width open
a band proof can instantiate this at each `w` instead, so a wider band names no new lemmas. -/
public theorem entrySeedLK_pair {lw lo start i w : Nat} (hw : w < 2 ^ lw) :
    entrySeedLK lw lo start (2 ^ lw * i + w)
      = Nat.add
          ((Nat.beq (w.land 1) 0).rec
            (firstLocK (indexK ((valueK (start + i)).mul 7)) lo ((valueK (start + i)).mul 2))
            (firstLocK (indexK ((valueK (start + i)).mul 5)) lo ((valueK (start + i)).mul 2)))
          (Nat.mul (w.shiftRight 1) ((valueK (start + i)).mul 2)) := by
  unfold entrySeedLK
  rw [shiftRightLw_pair hw, laneMaskK_eq, landLw_pair hw]
  rfl

/-- The same with the lane's two halves as `%` and `/`, which reduce when the lane is a literal.
This is what lets a band proof take its cases without a named lemma per lane. -/
public theorem entrySeedLK_lane {lw lo start i w : Nat} (hw : w < 2 ^ lw) :
    entrySeedLK lw lo start (2 ^ lw * i + w)
      = Nat.add
          ((Nat.beq (w % 2) 0).rec
            (firstLocK (indexK ((valueK (start + i)).mul 7)) lo ((valueK (start + i)).mul 2))
            (firstLocK (indexK ((valueK (start + i)).mul 5)) lo ((valueK (start + i)).mul 2)))
          (Nat.mul (w / 2) ((valueK (start + i)).mul 2)) := by
  have h1 : w.land 1 = w % 2 := landLw_eq (lw := 1)
  have h2 : w.shiftRight 1 = w / 2 := shiftRightLw_eq (lw := 1)
  rw [entrySeedLK_pair hw, h1, h2]

/-- Dividing by eight, two ways. -/
public theorem shiftRight3_eq {e : Nat} : e.shiftRight 3 = e / 8 := by
  have h : e.shiftRight 3 = e >>> 3 := rfl
  have h2 : (2 : Nat) ^ 3 = 8 := rfl
  rw [h, Nat.shiftRight_eq_div_pow, h2]

/-- The lowest three bits, two ways. -/
public theorem land7_eq {e : Nat} : e.land 7 = e % 8 := by
  have h : e.land 7 = e &&& (2 ^ 3 - 1) := rfl
  have h2 : (2 : Nat) ^ 3 = 8 := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod, h2]

/-- An entry is its position and which strike it names. -/
public theorem entry_split {e : Nat} : 8 * (e.shiftRight 3) + e.land 7 = e := by
  rw [shiftRight3_eq, land7_eq]
  have := Nat.div_add_mod e 8
  lia

/-- A strike is one of eight. -/
public theorem land_one_lt {e : Nat} : e.land 7 < 8 := by
  rw [land7_eq]
  exact Nat.mod_lt _ (by lia)

/-- The position an assembled entry names. -/
public theorem shiftRight1_pair {i w : Nat} (hw : w < 8) : (8 * i + w).shiftRight 3 = i := by
  rw [shiftRight3_eq]
  lia

/-- The strike an assembled entry names. -/
public theorem land1_pair {i w : Nat} (hw : w < 8) : (8 * i + w).land 7 = w := by
  rw [land7_eq]
  lia

/-- Every seed of every prime the batch holds lands in the assembled number, given that the tally
accounts for it. -/
public theorem stripeBatchK_complete {c lo start len W Wm1 slotW Ls Cs np i w : Nat}
    (hc2 : c < 2 ^ len) (hi : i < len) (hW : np * 65536 ≤ W) (hWm1 : Wm1 < W)
    (htally : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = true)
    (hX : entrySeedK lo start (8 * i + w) ≤ Wm1) :
    (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit
      (entrySeedK lo start (8 * i + w)) = true := by
  have hbatch : stripeBatchK c lo start len W Wm1 slotW Ls Cs np
      = stripeUpToK c lo start len W Wm1 slotW Ls Cs np (np + 1) := rfl
  rw [hbatch] at htally
  obtain ⟨k, hk65, hst⟩ :=
    (testBit_stripeUpToK_high (by lia : W ≤ W + (i + w * len)) hW (np + 1) (by lia)).mp htally
  have hJ : 65536 + (W + (i + w * len) - W) = 65536 + (i + w * len) := by lia
  rw [hJ] at hst
  -- an entry whose tally bit this is names position `i` and progression `w`
  have hentry : ∀ e : Nat, testBitK c (e.shiftRight 3) = true →
      entryTallyK len e = Nat.add 65536 (Nat.add i (Nat.mul w len)) → e = 8 * i + w := by
    intro e hce hte
    have hlt : e.shiftRight 3 < len := by
      by_contra hge
      rw [testBitK_of_lt hc2 (by lia)] at hce
      simp at hce
    obtain ⟨h1, h2⟩ := entryTallyK_inj hlt hi hte
    have := entry_split (e := e)
    lia
  rcases Nat.lt_or_ge k np with hk | hk64
  · have hstate : stripeStateK c lo start len Wm1 slotW Ls Cs np k
        = stripeSlotK c lo start k len
          ((Ls.shiftRight (slotW.mul k)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
          (cntOf Cs k) 0 := by
      unfold stripeStateK cntOf
      rw [beq_of_ne (by lia : k ≠ np)]
    rw [hstate] at hst
    rcases (testBit_stripeSlotK (cntOf Cs k)).mp hst with hz | ⟨m, hm, he⟩
    · simp at hz
    · unfold entryHits at he
      have h1 := (Bool.and_eq_true ..).mp he
      have h2 := (Bool.and_eq_true ..).mp h1.1
      have hbit : testBitK c ((entryOf Ls slotW k m).shiftRight 3) = true := h2.1
      have hk16 : (entrySeedK lo start (entryOf Ls slotW k m)).shiftRight 16 = k :=
        Nat.eq_of_beq_eq_true h2.2
      rcases (Bool.or_eq_true ..).mp h1.2 with hseed | htal
      · have hlow : 65536 + (i + w * len)
            = (entrySeedK lo start (entryOf Ls slotW k m)).land 65535 :=
          Nat.eq_of_beq_eq_true hseed
        rw [land65535_eq] at hlow
        have := Nat.mod_lt (entrySeedK lo start (entryOf Ls slotW k m)) (by lia : 0 < 65536)
        lia
      · have hte : entryTallyK len (entryOf Ls slotW k m)
            = Nat.add 65536 (Nat.add i (Nat.mul w len)) :=
          (Nat.eq_of_beq_eq_true htal).symm
        have heq : entryOf Ls slotW k m = 8 * i + w := hentry _ hbit hte
        exact (testBit_stripeBatchK_eq (by lia : entrySeedK lo start (8 * i + w) < W)).mpr
          ⟨k, m, hk, hm, hbit, hk16, by rw [heq]⟩
  · have hk64' : k = np := by lia
    rw [hk64'] at hst
    have hstate : stripeStateK c lo start len Wm1 slotW Ls Cs np np
        = stripeOutSlotK c lo start Wm1 len
          ((Ls.shiftRight (slotW.mul np)).land (Nat.sub (Nat.shiftLeft 1 slotW) 1))
          (cntOf Cs np) 0 := by
      have hbeq : Nat.beq np np = true := Nat.beq_eq.mpr rfl
      unfold stripeStateK cntOf
      rw [hbeq]
    rw [hstate] at hst
    rcases (testBit_stripeOutSlotK (cntOf Cs np)).mp hst with hz | ⟨m, hm, he⟩
    · simp at hz
    · unfold outHits at he
      have h1 := (Bool.and_eq_true ..).mp he
      have h2 := (Bool.and_eq_true ..).mp h1.1
      have hte : entryTallyK len (entryOf Ls slotW np m)
          = Nat.add 65536 (Nat.add i (Nat.mul w len)) := (Nat.eq_of_beq_eq_true h1.2).symm
      have hbit : testBitK c ((entryOf Ls slotW np m).shiftRight 3) = true := h2.1
      have heq : entryOf Ls slotW np m = 8 * i + w := hentry _ hbit hte
      have hblt : Nat.blt Wm1 (entrySeedK lo start (entryOf Ls slotW np m)) = true := h2.2
      rw [heq] at hblt
      have hble : Nat.ble (Wm1 + 1) (entrySeedK lo start (8 * i + w)) = true := hblt
      have := Nat.le_of_ble_eq_true hble
      lia

/-- A seed bit written relative to a 65536-bit slice of the window starting at `base`, and `0` when
the seed lies outside that slice. -/
@[expose] public noncomputable def seedStripeK (A base : Nat) : Nat :=
  (base.ble A).rec 0 (((A.sub base).ble 65535).rec 0 (Nat.shiftLeft 1 (A.sub base)))

/-- One prime's two seeds joined into a 65536-bit slice of the window rather than a number as wide
as the window. For a prime past half the window's width these two bits are all it can hit. -/
@[expose] public noncomputable def stripeMarkK (acc p lo _Wm1 base : Nat) : Nat :=
  acc.lor ((seedStripeK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) base).lor
    (seedStripeK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) base))

/-- `segLoopSCK` writing into a 65536-bit slice through `stripeMarkK`. -/
@[expose] public noncomputable def segLoopStripeK (c lo Wm1 base acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    (testBitK c i).rec a (stripeMarkK a (valueK (start.add i)) lo Wm1 base)

/-! ### A mask built to the window's width rather than to the next power of two

`buildMaskCK` doubles its span every round and stops once a further shift would pass the window,
so the span it finishes with lies between the window's width and twice it, and the last round is
the widest write of the lot. The definitions below take the round count `k` and a final shift `t`
from the emitter instead of guarding each round, with `t` the smallest multiple of the divisor's
period that lifts the span to the window's width. The pattern repeats with that period, so a
final shift by a multiple of it leaves the bits inside the window where they were.

The emitter is not trusted with `k` and `t`: `runSegmentV` computes the window this produces and
the window the existing twin produces, and refuses to emit if they differ. Prototype, so no
soundness is proved; the kernel checks each literal against the definition here. -/

/-- The span the doubling below finishes with: the period `2 * p`, doubled while a further
doubling would still fit inside the window. Scalar, so it costs nothing beside the mask. -/
@[expose] public noncomputable def spanEK (p M n : Nat) : Nat :=
  Nat.rec (p.mul 2)
    (fun i s => ((p.shiftLeft i.succ.succ).ble M.succ).rec s (s.mul 2)) n

/-- The shift that finishes the span: the smallest multiple of the period that lifts `spanEK` to
the window's width. The pattern repeats with that period, so shifting by a multiple of it leaves
the bits inside the window where they are. -/
@[expose] public noncomputable def shiftEK (p M n : Nat) : Nat :=
  (p.mul 2).mul
    (Nat.div (Nat.add (Nat.sub M.succ (spanEK p M n)) (Nat.sub (p.mul 2) 1)) (p.mul 2))

/-- `buildMaskCK` with the doubling stopped one round before it passes the window, and the span
then finished by a single shift. The mask it leaves spans the window and a little over, rather
than up to twice it.

The finishing shift is round 32 of the same fold rather than an operation applied to the fold's
result. Written the second way the fold appears twice in the term, and whether the kernel
evaluates such a repeat once or twice is not something measured here; this way the mask is a
bound value named twice, which is what `buildMaskCK` already does inside its own step. -/
@[expose] public noncomputable def buildMaskEK (p M A B n : Nat) : Nat :=
  Nat.rec ((seedK A M).lor (seedK B M))
    (fun i Mk =>
      (Nat.beq i n).rec
        (((p.shiftLeft i.succ.succ).ble M.succ).rec Mk
          (Mk.lor (Mk.shiftLeft (p.shiftLeft i.succ))))
        (Mk.lor (Mk.shiftLeft (shiftEK p M n))))
    n.succ

/-- `segMarkCK` with the mask built to the window's width. -/
@[expose] public noncomputable def segMarkEK (seg p lo Wm1 n : Nat) : Nat :=
  ((p.mul 2).ble Wm1).rec
    (clearHitK seg
      (seg.land ((seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
        (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1))))
    (clearHitK seg
      (seg.land (buildMaskEK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
        (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n)))

/-- `segLoopSCK` marking with `segMarkEK`, reading the divisors from the batch's own slice so that
the statement has the same shape as the one it is timed against. -/
@[expose] public noncomputable def segLoopEK (c lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkEK b (valueK (start.add i)) lo Wm1 n)

/-- The masks of a batch's divisors joined, each built to the window's width. The window is then
cleared once for the batch rather than once a divisor. Joining was measured three times against
masks built by doubling, which span up to twice the window, and lost each time; built to the
window's width the join carries a narrower number, which is what this asks again. -/
@[expose] public noncomputable def segAccLoopEK (c lo Wm1 n acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    (testBitK c i).rec a
      (a.lor (buildMaskEK (valueK (start.add i)) Wm1
        (firstLocK (indexK ((valueK (start.add i)).mul 5)) lo ((valueK (start.add i)).mul 2))
        (firstLocK (indexK ((valueK (start.add i)).mul 7)) lo ((valueK (start.add i)).mul 2)) n))

/-! ### One comb for both halves of a split window

A divisor's two progressions have stride `2 * p`, which is even, and their first positions differ
by `2 * index p + 1`, which is odd. So one progression lands entirely on even window positions and
the other entirely on odd ones, and neither ever crosses.

Split the window accordingly — even positions in the low half, odd positions in the high half —
and in half coordinates both progressions have stride `p`, differing only in where they start.
One comb of stride `p` therefore serves both, shifted into place twice. The comb is built at half
the window's width, where the doubling that dominates a divisor's cost writes half the bytes,
while the `land` and the subtraction stay full width.

The window this marks is a permutation of the usual one, so the emitter checks that unpermuting it
gives what the masks give. Prototype; nothing is proved. -/

/-- A comb of stride `p` from bit 0, doubled while it still fits in `M`. -/
@[expose] public noncomputable def combK (p M n : Nat) : Nat :=
  Nat.rec 1
    (fun i c => ((p.shiftLeft i).ble M).rec c (c.lor (c.shiftLeft (p.shiftLeft i))))
    n

/-- The hits of `p` on a split window: one comb, placed into each half at its own offset. The
placement is the fold's last round rather than an operation on its result, so the comb is a bound
value named twice, as `buildMaskCK`'s own step already does. -/
@[expose] public noncomputable def splitMaskK (p H Hm1 n aA aB : Nat) : Nat :=
  Nat.rec 1
    (fun i c =>
      (Nat.beq i n).rec
        (((p.shiftLeft i).ble Hm1).rec c (c.lor (c.shiftLeft (p.shiftLeft i))))
        -- Each placement is clamped to its own half. In the undivided window a mask may run past
        -- the end harmlessly, because the window has no bits there; here the low half's overflow
        -- would land on the high half and clear positions the divisor never strikes.
        ((Nat.land (c.shiftLeft aA) (Nat.sub (Nat.shiftLeft 1 H) 1)).lor
          ((Nat.land (c.shiftLeft aB) (Nat.sub (Nat.shiftLeft 1 H) 1)).shiftLeft H)))
    n.succ

/-- `segMarkCK` on a split window. The two starts are worked out here rather than supplied: one of
the usual pair is even and the other odd, and halving each gives its offset in its own half. -/
@[expose] public noncomputable def splitMarkK (seg p lo H Hm1 n : Nat) : Nat :=
  clearHitK seg
    (seg.land
      (splitMaskK p H Hm1 n
        ((Nat.beq (Nat.land (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) 1) 0).rec
          (Nat.shiftRight (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 1)
          (Nat.shiftRight (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) 1))
        ((Nat.beq (Nat.land (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) 1) 0).rec
          (Nat.shiftRight (Nat.sub (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) 1) 1)
          (Nat.shiftRight (Nat.sub (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 1) 1))))

/-- `segLoopSCK` on a split window. -/
@[expose] public noncomputable def splitLoopK (c lo H Hm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (splitMarkK b (valueK (start.add i)) lo H Hm1 n)

/-! ### Keeping what survives instead of removing what does not

`segMarkCK` builds the divisor's hits, ands them into the window and subtracts: a compare, two
copies of the window and a subtraction pass beyond the mask construction itself. The complement
costs the same to build — the pattern repeats with the same period `2 * p`, so the same doubling
tiles it — and then marking is one `land` and nothing else.

The seed is one period with the two strike positions cleared. Those positions are always distinct:
`index (7p) - index (5p)` is `2 * index p + 1`, which is odd, and the period is even, so they
cannot coincide. Prototype; the emitter checks it clears the window the masks clear. -/

/-- One period of the complement: `2 * p` ones with the two strike positions removed. -/
@[expose] public noncomputable def seedCompK (p A B : Nat) : Nat :=
  Nat.sub (Nat.sub (Nat.sub (Nat.shiftLeft 1 (p.mul 2)) 1) (Nat.shiftLeft 1 A))
    (Nat.shiftLeft 1 B)

/-- That period tiled to the window by the doubling `buildMaskCK` uses. -/
@[expose] public noncomputable def buildCompK (p M A B n : Nat) : Nat :=
  Nat.rec (seedCompK p A B)
    (fun i Mk => ((p.shiftLeft i.succ).ble M).rec Mk
      (Mk.lor (Mk.shiftLeft (p.shiftLeft i.succ))))
    n

/-- Marking by keeping: one `land`, no compare and no subtraction. -/
@[expose] public noncomputable def segMarkKeepK (seg p lo Wm1 n : Nat) : Nat :=
  seg.land (buildCompK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
    (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n)

/-- `segLoopSCK` marking by keeping. -/
@[expose] public noncomputable def segLoopKeepK (c lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkKeepK b (valueK (start.add i)) lo Wm1 n)

/-! ### One mask for the four smallest divisors

Each divisor's mask repeats with period `2 * p`, so the union of 5, 7, 11 and 13 repeats with
period `2 * 5 * 7 * 11 * 13 = 10010` positions. That union can be built once at 10010 bits, where
the numbers are small, and then doubled to the window, instead of four masks each doubled all the
way. The window's width caps which divisors can share this way: the next prime takes the period
to 170170 and then 3233230, past which nothing fits, so at most six divisors of the small band's
43390 are ever eligible.

The arithmetic therefore says the ceiling is a few thousandths of a percent, and this exists
because Bhavik asked for it to be measured rather than rejected on that arithmetic. Prototype,
no soundness proved; the kernel checks the literal. -/

/-- 5, 7, 11, 13, five bits each. -/
@[expose] public def comboSetK : Nat := 437477

/-- The union of those four divisors' masks across one shared period of 10010 positions. -/
@[expose] public noncomputable def comboBaseK (lo : Nat) : Nat :=
  Nat.rec 0
    (fun j acc =>
      acc.lor
        (buildMaskCK (Nat.land (Nat.shiftRight comboSetK (Nat.mul 5 j)) 31) 10009
          (firstLocK (indexK ((Nat.land (Nat.shiftRight comboSetK (Nat.mul 5 j)) 31).mul 5)) lo
            ((Nat.land (Nat.shiftRight comboSetK (Nat.mul 5 j)) 31).mul 2))
          (firstLocK (indexK ((Nat.land (Nat.shiftRight comboSetK (Nat.mul 5 j)) 31).mul 7)) lo
            ((Nat.land (Nat.shiftRight comboSetK (Nat.mul 5 j)) 31).mul 2)) 14))
    4

/-- That shared period tiled up to the window by doubling. -/
@[expose] public noncomputable def comboMaskK (lo M : Nat) : Nat :=
  Nat.rec (comboBaseK lo)
    (fun i Mk => ((Nat.shiftLeft 10010 i).ble M).rec Mk
      (Mk.lor (Mk.shiftLeft (Nat.shiftLeft 10010 i))))
    12

/-- The window with all four of those divisors cleared at once. -/
@[expose] public noncomputable def comboClearK (seg lo M : Nat) : Nat :=
  clearHitK seg (seg.land (comboMaskK lo M))

/-- `segMarkCK` with the mask in the closed form of `buildMaskRK`. -/
@[expose] public noncomputable def segMarkRK (seg p lo Wm1 : Nat) : Nat :=
  clearHitK seg
    ((buildMaskRK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
      (firstLocK (indexK (p.mul 7)) lo (p.mul 2))).land seg)

/-- `segLoopSCK` marking with `segMarkRK`. -/
@[expose] public noncomputable def segLoopSRK (c lo Wm1 seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkRK b (valueK (start.add i)) lo Wm1)

/-- `segMarkCK` with the mask built to the window's own width by `buildMaskNK`. -/
@[expose] public noncomputable def segMarkNK (seg p lo Wm1 n : Nat) : Nat :=
  clearHitK seg
    ((buildMaskNK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
      (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n).land seg)

/-- `segLoopSCK` marking with `segMarkNK`. -/
@[expose] public noncomputable def segLoopSNK (c lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkNK b (valueK (start.add i)) lo Wm1 n)

/-- One prime's mask joined into a running mask, leaving the window untouched. -/
@[expose] public noncomputable def segAccK (acc p lo Wm1 n : Nat) : Nat :=
  acc.lor (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
    (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n)

/-- The masks of a stretch of base primes joined into one, read from the slice `c` of the base
sieve. The window is cleared once against the result, in place of once per prime. -/
@[expose] public noncomputable def segAccLoopSK (c lo Wm1 n acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    (testBitK c i).rec a (segAccK a (valueK (start.add i)) lo Wm1 n)

/-- `segAccLoopSK` reading the base primes from the base sieve itself. -/
@[expose] public noncomputable def segAccLoopK (s lo Wm1 n acc start fuel : Nat) : Nat :=
  fuel.rec acc fun i a =>
    (testBitK s (start.add i)).rec a (segAccK a (valueK (start.add i)) lo Wm1 n)

/-- Loop recurrence for `segLoopCK`. -/
public theorem segLoopCK_succ {s lo Wm1 n seg start fuel : Nat} :
    segLoopCK s lo Wm1 n seg start (fuel + 1)
      = Bool.rec (segLoopCK s lo Wm1 n seg start fuel)
          (segMarkCK (segLoopCK s lo Wm1 n seg start fuel) (valueK (start + fuel)) lo Wm1 n)
          (testBitK s (start + fuel)) := rfl

/-- Fuel additivity for `segLoopCK`. -/
public theorem segLoopCK_add {s lo Wm1 n seg start a b : Nat} :
    segLoopCK s lo Wm1 n seg start (a + b)
      = segLoopCK s lo Wm1 n (segLoopCK s lo Wm1 n seg start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [segLoopCK_succ]

/-- One chain step for `segLoopCK`. -/
public theorem segLoopCK_chain {L s lo Wm1 n b b' start len rest : Nat}
    (hP : L = segLoopCK s lo Wm1 n b start (len.add rest))
    (h : (segLoopCK s lo Wm1 n b start len).beq b') :
    L = segLoopCK s lo Wm1 n b' (start.add len) rest := by
  grind [segLoopCK_add, Nat.beq_eq]

/-- Last chain step for `segLoopCK`. -/
public theorem segLoopCK_last {L s lo Wm1 n b b' start len : Nat}
    (hP : L = segLoopCK s lo Wm1 n b start len)
    (h : (segLoopCK s lo Wm1 n b start len).beq b') :
    L = b' := by
  grind [Nat.beq_eq]

/-! ### Joining two stretches of a run

The chain lemmas above move one batch at a time, so a run of `k` batches is a term nesting `k`
deep. These two join a pair of neighbouring stretches instead, so the emitter can combine batches
in a tree, each node its own declaration. -/

/-- A batch equation in `Eq` form. -/
public theorem segLoopK_of_beq {s lo Wm1 b b' start len : Nat}
    (h : (segLoopK s lo Wm1 b start len).beq b') : segLoopK s lo Wm1 b start len = b' :=
  Nat.beq_eq.mp h

/-- A clamped batch equation in `Eq` form. -/
public theorem segLoopCK_of_beq {s lo Wm1 n b b' start len : Nat}
    (h : (segLoopCK s lo Wm1 n b start len).beq b') : segLoopCK s lo Wm1 n b start len = b' :=
  Nat.beq_eq.mp h

/-- Two neighbouring stretches join into one. -/
public theorem segLoopK_join {s lo Wm1 b b' b'' start len rest : Nat}
    (h1 : segLoopK s lo Wm1 b start len = b')
    (h2 : segLoopK s lo Wm1 b' (start.add len) rest = b'') :
    segLoopK s lo Wm1 b start (len.add rest) = b'' := by
  rw [Nat.add_eq, segLoopK_add, h1]
  rwa [Nat.add_eq] at h2

/-- Two neighbouring clamped stretches join into one. -/
public theorem segLoopCK_join {s lo Wm1 n b b' b'' start len rest : Nat}
    (h1 : segLoopCK s lo Wm1 n b start len = b')
    (h2 : segLoopCK s lo Wm1 n b' (start.add len) rest = b'') :
    segLoopCK s lo Wm1 n b start (len.add rest) = b'' := by
  rw [Nat.add_eq, segLoopCK_add, h1]
  rwa [Nat.add_eq] at h2

/-! ### From the clamped marking back to `segMarkK`

`segMarkCK` drops seed bits above the window, runs `n` doubling rounds in place of 32, skips the
rounds entirely for a prime wider than the window, and leaves the window alone when nothing hits.
The lemmas below show it clears exactly the bits `segMarkK` clears, for any window below
`2 ^ (Wm1 + 1)`. -/

/-- `clearHitK` subtracts its second argument. -/
public theorem clearHitK_eq {seg hit : Nat} : clearHitK seg hit = seg - hit := by
  cases hit <;> rfl

/-- Two masks agreeing below `M` clear the same bits of a window below `2 ^ (M + 1)`. -/
public theorem land_congr_below {seg x y M : Nat} (hseg : seg < 2 ^ (M + 1))
    (h : ∀ i ≤ M, x.testBit i = y.testBit i) : seg.land x = seg.land y := by
  have hx : seg.land x = seg &&& x := rfl
  have hy : seg.land y = seg &&& y := rfl
  rw [hx, hy]
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [Nat.testBit_and]
  rcases Nat.lt_or_ge M i with hi | hi
  · have h2 : (2 : ℕ) ^ (M + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by lia) (by lia)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hseg h2)]
    simp
  · rw [h i hi]

/-- `seedK` in ordinary notation. -/
public theorem seedK_eq {A M : Nat} : seedK A M = if A ≤ M then 1 <<< A else 0 := by
  unfold seedK
  cases hb : Nat.ble A M with
  | true =>
    have h : A ≤ M := by grind [Nat.ble_eq]
    simp [h]
  | false =>
    have h : ¬ A ≤ M := by grind [Nat.ble_eq]
    simp [h]

/-- Below `M`, a clamped seed is the seed. -/
public theorem seedK_testBit {A M i : Nat} (hi : i ≤ M) :
    (seedK A M).testBit i = (1 <<< A : Nat).testBit i := by
  rw [seedK_eq]
  by_cases hA : A ≤ M
  · rw [if_pos hA]
  · rw [if_neg hA]
    have : A ≠ i := by lia
    simp [Nat.shiftLeft_eq, this]

/-- Both masks start from their two seeds. -/
public theorem buildMaskCK_zero {p M A B : Nat} :
    buildMaskCK p M A B 0 = seedK A M ||| seedK B M := rfl

/-- The mask starts from its two seeds. -/
public theorem buildMaskK_zero' {p M A B : Nat} :
    buildMaskK p M A B 0 = 1 <<< A ||| 1 <<< B := rfl

/-- Round recurrence for `buildMaskCK`, in the `Bool.rec` form the definition uses. -/
public theorem buildMaskCK_succ_raw {p M A B n : Nat} :
    buildMaskCK p M A B (n + 1)
      = Bool.rec (buildMaskCK p M A B n)
          ((buildMaskCK p M A B n).lor
            ((buildMaskCK p M A B n).shiftLeft (p.shiftLeft n.succ)))
          ((p.shiftLeft n.succ).ble M) := rfl

/-- Round recurrence for `buildMaskK`, in the `Bool.rec` form the definition uses. -/
public theorem buildMaskK_succ_raw' {p M A B n : Nat} :
    buildMaskK p M A B (n + 1)
      = Bool.rec (buildMaskK p M A B n)
          ((buildMaskK p M A B n).lor ((buildMaskK p M A B n).shiftLeft (p.shiftLeft n.succ)))
          ((p.shiftLeft n.succ).ble M) := rfl

/-- Round recurrence for `buildMaskCK`, in ordinary notation. -/
public theorem buildMaskCK_succ {p M A B n : Nat} :
    buildMaskCK p M A B (n + 1)
      = if p * 2 ^ (n + 1) ≤ M
        then buildMaskCK p M A B n ||| buildMaskCK p M A B n <<< (p * 2 ^ (n + 1))
        else buildMaskCK p M A B n := by
  have hs : p <<< (n + 1) = p * 2 ^ (n + 1) := by grind [Nat.shiftLeft_eq]
  simp [buildMaskCK_succ_raw, hs, Bool.rec_eq]

/-- Round recurrence for `buildMaskK`, in ordinary notation. -/
public theorem buildMaskK_succ' {p M A B n : Nat} :
    buildMaskK p M A B (n + 1)
      = if p * 2 ^ (n + 1) ≤ M
        then buildMaskK p M A B n ||| buildMaskK p M A B n <<< (p * 2 ^ (n + 1))
        else buildMaskK p M A B n := by
  have hs : p <<< (n + 1) = p * 2 ^ (n + 1) := by grind [Nat.shiftLeft_eq]
  simp [buildMaskK_succ_raw', hs, Bool.rec_eq]

/-- A prime wider than the window gets no rounds, whatever `n` says. -/
public theorem buildMaskCK_wide {p M A B n : Nat} (hw : M < p * 2) :
    buildMaskCK p M A B n = buildMaskCK p M A B 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [buildMaskCK_succ, ih]
    have hle : p * 2 ≤ p * 2 ^ (n + 1) := by
      have h2 : (2 : Nat) ≤ 2 ^ (n + 1) := Nat.one_lt_two_pow (by lia)
      exact Nat.mul_le_mul_left p h2
    rw [if_neg (by lia)]

/-- A divisor whose double fits the window and whose quadruple does not gets exactly one round,
whatever `n` says beyond the first. -/
public theorem buildMaskCK_band {p M A B n : Nat} (h4 : M < p * 4) (hn : 1 ≤ n) :
    buildMaskCK p M A B n = buildMaskCK p M A B 1 := by
  induction n with
  | zero => exact absurd hn (by lia)
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with h | h
    · rw [← h]
    · have hn' : 1 ≤ n := by lia
      rw [buildMaskCK_succ, ih hn']
      have hle : p * 4 ≤ p * 2 ^ (n + 1) := by
        have h2 : (4 : Nat) ≤ 2 ^ (n + 1) := by
          have hx : (2 : Nat) ^ 2 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by lia) (by lia)
          have hy : (2 : Nat) ^ 2 = 4 := rfl
          rw [hy] at hx
          exact hx
        exact Nat.mul_le_mul_left p h2
      rw [if_neg (by lia)]

/-- That one round is the two clamped seeds joined with the same two a double along. -/
public theorem buildMaskCK_one {p M A B : Nat} (h2 : p * 2 ≤ M) :
    buildMaskCK p M A B 1
      = (seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< (p * 2) := by
  have hp : (2 : Nat) ^ (0 + 1) = 2 := rfl
  rw [buildMaskCK_succ, hp, if_pos h2, buildMaskCK_zero]

/-- A divisor whose quadruple fits the window and whose octuple does not gets exactly two rounds,
whatever `n` says beyond the second. -/
public theorem buildMaskCK_octave {p M A B n : Nat} (h8 : M < p * 8) (hn : 2 ≤ n) :
    buildMaskCK p M A B n = buildMaskCK p M A B 2 := by
  induction n with
  | zero => exact absurd hn (by lia)
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with h | h
    · rw [← h]
    · have hn' : 2 ≤ n := by lia
      rw [buildMaskCK_succ, ih hn']
      have h2 : (8 : Nat) ≤ 2 ^ (n + 1) := by
        have hx : (2 : Nat) ^ 3 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by lia) (by lia)
        have hy : (2 : Nat) ^ 3 = 8 := rfl
        rw [hy] at hx
        exact hx
      have hle : p * 8 ≤ p * 2 ^ (n + 1) := Nat.mul_le_mul_left p h2
      rw [if_neg (by lia)]

/-- Those two rounds are the one-round mask joined with the same mask a quadruple along. -/
public theorem buildMaskCK_two {p M A B : Nat} (h2 : p * 2 ≤ M) (h4 : p * 4 ≤ M) :
    buildMaskCK p M A B 2
      = ((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< (p * 2))
        ||| ((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< (p * 2)) <<< (p * 4) := by
  have hp : (2 : Nat) ^ (1 + 1) = 4 := rfl
  rw [buildMaskCK_succ, hp, if_pos h4, buildMaskCK_one h2]

/-- The octave below: where the divisor's sixteenfold passes the window's end, three rounds are
all the mask ever gets, however many it is given. -/
public theorem buildMaskCK_hexa {p M A B n : Nat} (h16 : M < p * 16) (hn : 3 ≤ n) :
    buildMaskCK p M A B n = buildMaskCK p M A B 3 := by
  induction n with
  | zero => exact absurd hn (by lia)
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with h | h
    · rw [← h]
    · have hn' : 3 ≤ n := by lia
      rw [buildMaskCK_succ, ih hn']
      have h2 : (16 : Nat) ≤ 2 ^ (n + 1) := by
        have hx : (2 : Nat) ^ 4 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by lia) (by lia)
        have hy : (2 : Nat) ^ 4 = 16 := rfl
        rw [hy] at hx
        exact hx
      have hle : p * 16 ≤ p * 2 ^ (n + 1) := Nat.mul_le_mul_left p h2
      rw [if_neg (by lia)]

/-- Those three rounds are the two-round mask joined with the same mask an octuple along. -/
public theorem buildMaskCK_three {p M A B : Nat} (h8 : p * 8 ≤ M) :
    buildMaskCK p M A B 3
      = buildMaskCK p M A B 2 ||| (buildMaskCK p M A B 2) <<< (p * 8) := by
  have hp : (2 : Nat) ^ (2 + 1) = 8 := rfl
  rw [buildMaskCK_succ, hp, if_pos h8]

/-- Below `M`, the clamped mask is the mask. -/
public theorem buildMaskCK_testBit {p M A B n : Nat} :
    ∀ i ≤ M, (buildMaskCK p M A B n).testBit i = (buildMaskK p M A B n).testBit i := by
  induction n with
  | zero =>
    intro i hi
    rw [buildMaskCK_zero, buildMaskK_zero', Nat.testBit_or, Nat.testBit_or, seedK_testBit hi,
      seedK_testBit hi]
  | succ n ih =>
    intro i hi
    rw [buildMaskCK_succ, buildMaskK_succ']
    by_cases hc : p * 2 ^ (n + 1) ≤ M
    · rw [if_pos hc, if_pos hc, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.testBit_shiftLeft, ih i hi]
      rcases Nat.lt_or_ge i (p * 2 ^ (n + 1)) with hlt | hge
      · simp [Nat.not_le_of_lt hlt]
      · rw [ih (i - p * 2 ^ (n + 1)) (by lia)]
    · rw [if_neg hc, if_neg hc]
      exact ih i hi

/-- Rounds past the width of the window change nothing. -/
public theorem buildMaskK_rounds {p M A B n : Nat} (hp : 1 ≤ p) (hM : M < 2 ^ n) :
    ∀ m, n ≤ m → buildMaskK p M A B m = buildMaskK p M A B n := by
  intro m
  induction m with
  | zero => intro h; grind
  | succ m ih =>
    intro h
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm : n ≤ m := by lia
      have h1 : (2 : ℕ) ^ n ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by lia) (by lia)
      have h3 : 1 * 2 ^ (m + 1) ≤ p * 2 ^ (m + 1) := Nat.mul_le_mul_right _ hp
      have hbig : ¬ (p * 2 ^ (m + 1) ≤ M) := by lia
      rw [buildMaskK_succ', if_neg hbig]
      exact ih hnm
    · have hnm : n = m + 1 := by lia
      rw [hnm]

/-- Rounds past the point where a divisor's own stride covers the window change nothing, which is
a weaker requirement on the round count than the window's own width gives. -/
public theorem buildMaskK_rounds_stride {p M A B n : Nat} (hM : M < p * 2 ^ (n + 1)) :
    ∀ m, n ≤ m → buildMaskK p M A B m = buildMaskK p M A B n := by
  intro m
  induction m with
  | zero => intro h; grind
  | succ m ih =>
    intro h
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have hnm : n ≤ m := by lia
      have h1 : p * 2 ^ (n + 1) ≤ p * 2 ^ (m + 1) :=
        Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by lia) (by lia))
      have hbig : ¬ (p * 2 ^ (m + 1) ≤ M) := by lia
      rw [buildMaskK_succ', if_neg hbig]
      exact ih hnm
    · have hnm : n = m + 1 := by lia
      rw [hnm]

/-- For a prime wider than the window, every round is a no-op. -/
public theorem buildMaskK_rounds_wide {p M A B : Nat} (hw : M < p * 2) :
    ∀ m, buildMaskK p M A B m = buildMaskK p M A B 0 := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : p * 2 ≤ p * 2 ^ (m + 1) := by
      have : (2 : ℕ) ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by lia) (by lia)
      have h2 : p * 2 ^ 1 ≤ p * 2 ^ (m + 1) := Nat.mul_le_mul_left _ this
      lia
    rw [buildMaskK_succ', if_neg (by lia)]
    exact ih

/-- A window never grows as the loop runs. -/
public theorem segLoopK_le {s lo Wm1 seg start fuel : Nat} :
    segLoopK s lo Wm1 seg start fuel ≤ seg := by
  induction fuel with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [segLoopK_succ]
    cases testBitK s (start + n) with
    | false => exact ih
    | true => exact Nat.le_trans (Nat.sub_le _ _) ih

/-- Every position names a positive number. -/
public theorem one_le_valueK {k : Nat} : 1 ≤ valueK k := by
  unfold valueK
  lia

/-- The clamped marking removes the prime's mask from the window. -/
public theorem segMarkCK_ldiff {seg p lo Wm1 n : Nat} :
    segMarkCK seg p lo Wm1 n
      = Nat.ldiff seg (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n) := by
  have hite : segMarkCK seg p lo Wm1 n
      = if p * 2 ≤ Wm1
        then clearHitK seg ((buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n).land seg)
        else clearHitK seg ((buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 0).land seg) := by
    simp [segMarkCK, Bool.rec_eq, Nat.ble_eq, Nat.mul_eq, buildMaskCK_zero, Nat.land_comm]
  have hland : ∀ m : Nat, Nat.ldiff seg m = seg - m.land seg := by
    intro m
    have h1 : m.land seg = seg &&& m := Nat.land_comm m seg
    rw [h1, Nat.sub_and_eq_ldiff]
  rw [hite, hland]
  by_cases hc : p * 2 ≤ Wm1
  · rw [if_pos hc, clearHitK_eq]
  · have hwide : buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
        (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n
        = buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 0 := buildMaskCK_wide (by lia)
    rw [if_neg hc, clearHitK_eq, hwide]

/-- Removing a mask, written with the two operations the kernel reduces directly. -/
public theorem ldiff_eq_sub {seg m : Nat} : Nat.ldiff seg m = Nat.sub seg (Nat.land m seg) := by
  have h1 : Nat.land m seg = seg &&& m := Nat.land_comm m seg
  have h2 : Nat.sub seg (seg &&& m) = seg - (seg &&& m) := rfl
  rw [h1, h2, Nat.sub_and_eq_ldiff]

/-- Removing two masks one after the other removes their union. -/
public theorem ldiff_ldiff {seg m1 m2 : Nat} :
    Nat.ldiff (Nat.ldiff seg m1) m2 = Nat.ldiff seg (m1 ||| m2) := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp [Nat.testBit_ldiff, Nat.testBit_or, Bool.and_assoc]

/-- The clamped marking clears exactly the bits the marking clears, for a window inside the
range. -/
public theorem segMarkCK_eq {seg p lo Wm1 n : Nat} (hseg : seg < 2 ^ (Wm1 + 1)) (hp : 1 ≤ p)
    (hn : Wm1 < 2 ^ n) (hn32 : n ≤ 32) :
    segMarkCK seg p lo Wm1 n = segMarkK seg p lo Wm1 := by
  have hite : segMarkCK seg p lo Wm1 n
      = if p * 2 ≤ Wm1
        then clearHitK seg (seg.land (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n))
        else clearHitK seg (seg.land
          ((seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
            (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1))) := by
    simp [segMarkCK, Bool.rec_eq, Nat.ble_eq, Nat.mul_eq]
  have hsub : ∀ x : Nat, seg.sub x = seg - x := fun _ => rfl
  rw [hite, segMarkK, hsub]
  by_cases hc : p * 2 ≤ Wm1
  · rw [if_pos hc, clearHitK_eq, buildMaskK_rounds hp hn 32 hn32,
      land_congr_below hseg fun i hi => buildMaskCK_testBit i hi]
  · have hw : Wm1 < p * 2 := by lia
    have hseed : (seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
        (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1)
        = buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 0 := rfl
    rw [if_neg hc, clearHitK_eq, hseed, buildMaskK_rounds_wide hw 32,
      land_congr_below hseg fun i hi => buildMaskCK_testBit i hi]

/-- The value of a base index in ordinary notation. -/
public theorem valueK_eq_add {k : Nat} : valueK k = k * 3 + 1 + k % 2 := rfl

/-- Later base indices name larger numbers. -/
public theorem valueK_le {i j : Nat} (h : i ≤ j) : valueK i ≤ valueK j := by
  rw [valueK_eq_add, valueK_eq_add]
  have hi : i % 2 < 2 := Nat.mod_lt _ (by lia)
  have hj : j % 2 < 2 := Nat.mod_lt _ (by lia)
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · lia
  · lia

/-- The same where the round count is measured against the divisor's own stride rather than the
window's width, which is what lets a batch of large divisors be given fewer rounds. -/
public theorem segMarkCK_eq_stride {seg p lo Wm1 n : Nat} (hseg : seg < 2 ^ (Wm1 + 1))
    (hn : Wm1 < p * 2 ^ (n + 1)) (hn32 : n ≤ 32) :
    segMarkCK seg p lo Wm1 n = segMarkK seg p lo Wm1 := by
  have hite : segMarkCK seg p lo Wm1 n
      = if p * 2 ≤ Wm1
        then clearHitK seg (seg.land (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n))
        else clearHitK seg (seg.land
          ((seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
            (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1))) := by
    simp [segMarkCK, Bool.rec_eq, Nat.ble_eq, Nat.mul_eq]
  have hsub : ∀ x : Nat, seg.sub x = seg - x := fun _ => rfl
  rw [hite, segMarkK, hsub]
  by_cases hc : p * 2 ≤ Wm1
  · rw [if_pos hc, clearHitK_eq, buildMaskK_rounds_stride hn 32 hn32,
      land_congr_below hseg fun i hi => buildMaskCK_testBit i hi]
  · have hw : Wm1 < p * 2 := by lia
    have hseed : (seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
        (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1)
        = buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 0 := rfl
    rw [if_neg hc, clearHitK_eq, hseed, buildMaskK_rounds_wide hw 32,
      land_congr_below hseg fun i hi => buildMaskCK_testBit i hi]

/-- A batch whose smallest divisor's stride already covers the window in `n` rounds runs the same
way as the unclamped loop, whatever the window's own width would ask for. -/
public theorem segLoopCK_eq_stride {s lo Wm1 n seg start fuel : Nat} (hseg : seg < 2 ^ (Wm1 + 1))
    (hn : Wm1 < valueK start * 2 ^ (n + 1)) (hn32 : n ≤ 32) :
    segLoopCK s lo Wm1 n seg start fuel = segLoopK s lo Wm1 seg start fuel := by
  induction fuel with
  | zero => rfl
  | succ m ih =>
    rw [segLoopCK_succ, segLoopK_succ, ih]
    cases testBitK s (start + m) with
    | false => rfl
    | true =>
      have hle : valueK start ≤ valueK (start + m) := valueK_le (by lia)
      have hmul : valueK start * 2 ^ (n + 1) ≤ valueK (start + m) * 2 ^ (n + 1) :=
        Nat.mul_le_mul_right _ hle
      exact segMarkCK_eq_stride (Nat.lt_of_le_of_lt segLoopK_le hseg) (by lia) hn32

/-- Loop recurrence for `segLoopCK`, with the window bound carried along. -/
public theorem segLoopCK_eq {s lo Wm1 n seg start fuel : Nat} (hseg : seg < 2 ^ (Wm1 + 1))
    (hn : Wm1 < 2 ^ n) (hn32 : n ≤ 32) :
    segLoopCK s lo Wm1 n seg start fuel = segLoopK s lo Wm1 seg start fuel := by
  induction fuel with
  | zero => rfl
  | succ m ih =>
    rw [segLoopCK_succ, segLoopK_succ, ih]
    cases testBitK s (start + m) with
    | false => rfl
    | true =>
      exact segMarkCK_eq (Nat.lt_of_le_of_lt segLoopK_le hseg) one_le_valueK hn hn32

/-- The window a run starts from is inside the range. -/
public theorem initSegK_lt {W : Nat} : initSegK W < 2 ^ W := by
  unfold initSegK
  have hs : Nat.shiftLeft 1 W = 1 <<< W := rfl
  have h : (1 : Nat) <<< W = 2 ^ W := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hpos : 0 < 2 ^ W := Nat.two_pow_pos W
  rw [hs, h]
  lia

/-- Loop recurrence for `segLoopSCK`. -/
public theorem segLoopSCK_succ {c lo Wm1 n seg start fuel : Nat} :
    segLoopSCK c lo Wm1 n seg start (fuel + 1)
      = Bool.rec (segLoopSCK c lo Wm1 n seg start fuel)
          (segMarkCK (segLoopSCK c lo Wm1 n seg start fuel) (valueK (start + fuel)) lo Wm1 n)
          (testBitK c fuel) := rfl

/-- Loop recurrence for `segAccLoopSK`. -/
public theorem segAccLoopSK_succ {c lo Wm1 n acc start fuel : Nat} :
    segAccLoopSK c lo Wm1 n acc start (fuel + 1)
      = Bool.rec (segAccLoopSK c lo Wm1 n acc start fuel)
          (segAccK (segAccLoopSK c lo Wm1 n acc start fuel) (valueK (start + fuel)) lo Wm1 n)
          (testBitK c fuel) := rfl

/-- A joining step in ordinary notation, with the new mask first. -/
public theorem segAccK_eq {acc p lo Wm1 n : Nat} :
    segAccK acc p lo Wm1 n
      = buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
          (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n ||| acc := by
  unfold segAccK
  have hor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  rw [hor, Nat.lor_comm]

/-- Anything joined into the accumulator before a batch can be joined after it instead. -/
public theorem segAccLoopSK_lor {c lo Wm1 n x acc start fuel : Nat} :
    segAccLoopSK c lo Wm1 n (x ||| acc) start fuel
      = x ||| segAccLoopSK c lo Wm1 n acc start fuel := by
  induction fuel with
  | zero => rfl
  | succ m ih =>
    rw [segAccLoopSK_succ, segAccLoopSK_succ]
    cases testBitK c m with
    | false => exact ih
    | true =>
      simp only [segAccK_eq, ih]
      rw [← Nat.lor_assoc, ← Nat.lor_assoc, Nat.lor_comm (buildMaskCK _ _ _ _ _) x]

/-- Loop recurrence for `segAccLoopK`. -/
public theorem segAccLoopK_succ {s lo Wm1 n acc start fuel : Nat} :
    segAccLoopK s lo Wm1 n acc start (fuel + 1)
      = Bool.rec (segAccLoopK s lo Wm1 n acc start fuel)
          (segAccK (segAccLoopK s lo Wm1 n acc start fuel) (valueK (start + fuel)) lo Wm1 n)
          (testBitK s (start + fuel)) := rfl

/-- Fuel additivity for `segAccLoopK`. -/
public theorem segAccLoopK_add {s lo Wm1 n acc start a b : Nat} :
    segAccLoopK s lo Wm1 n acc start (a + b)
      = segAccLoopK s lo Wm1 n (segAccLoopK s lo Wm1 n acc start a) (start + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => grind [segAccLoopK_succ]

/-- One chain step for `segAccLoopK`. -/
public theorem segAccLoopK_chain {L s lo Wm1 n acc acc' start len rest : Nat}
    (hP : L = segAccLoopK s lo Wm1 n acc start (len.add rest))
    (h : (segAccLoopK s lo Wm1 n acc start len).beq acc') :
    L = segAccLoopK s lo Wm1 n acc' (start.add len) rest := by
  grind [segAccLoopK_add, Nat.beq_eq]

/-- Last chain step for `segAccLoopK`. -/
public theorem segAccLoopK_last {L s lo Wm1 n acc acc' start len : Nat}
    (hP : L = segAccLoopK s lo Wm1 n acc start len)
    (h : (segAccLoopK s lo Wm1 n acc start len).beq acc') : L = acc' := by
  grind [Nat.beq_eq]

/-- A slice agreeing with the base sieve on the batch's positions joins the same masks. -/
public theorem segAccLoopSK_eq {c s lo Wm1 n acc start len : Nat}
    (h : ∀ i < len, testBitK c i = testBitK s (start + i)) :
    segAccLoopSK c lo Wm1 n acc start len = segAccLoopK s lo Wm1 n acc start len := by
  induction len with
  | zero => rfl
  | succ m ih =>
    rw [segAccLoopSK_succ, segAccLoopK_succ, ih fun i hi => h i (by lia), h m (by lia)]

/-- Anything joined into the accumulator before a run can be joined after it instead. -/
public theorem segAccLoopK_lor {s lo Wm1 n x acc start fuel : Nat} :
    segAccLoopK s lo Wm1 n (x ||| acc) start fuel
      = x ||| segAccLoopK s lo Wm1 n acc start fuel := by
  induction fuel with
  | zero => rfl
  | succ m ih =>
    rw [segAccLoopK_succ, segAccLoopK_succ]
    cases testBitK s (start + m) with
    | false => exact ih
    | true =>
      simp only [segAccK_eq, ih]
      rw [← Nat.lor_assoc, ← Nat.lor_assoc, Nat.lor_comm (buildMaskCK _ _ _ _ _) x]

/-- A run's accumulator splits into the run's own masks and whatever it started from. -/
public theorem segAccLoopK_zero {s lo Wm1 n acc start fuel : Nat} :
    segAccLoopK s lo Wm1 n acc start fuel = segAccLoopK s lo Wm1 n 0 start fuel ||| acc := by
  have h := segAccLoopK_lor (s := s) (lo := lo) (Wm1 := Wm1) (n := n) (x := acc) (acc := 0)
    (start := start) (fuel := fuel)
  have hz : acc ||| 0 = acc := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  rw [hz] at h
  rw [h, Nat.lor_comm]

/-- A batch's accumulator splits into the batch's own masks and whatever it started from. -/
public theorem segAccLoopSK_zero {c lo Wm1 n acc start fuel : Nat} :
    segAccLoopSK c lo Wm1 n acc start fuel = segAccLoopSK c lo Wm1 n 0 start fuel ||| acc := by
  have h := segAccLoopSK_lor (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (x := acc) (acc := 0)
    (start := start) (fuel := fuel)
  have hz : acc ||| 0 = acc := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  rw [hz] at h
  rw [h, Nat.lor_comm]

/-- Clearing the window once against the joined masks of a batch gives what clearing it once per
prime gives. -/
public theorem segLoopSCK_eq_ldiff {c lo Wm1 n seg acc start fuel : Nat} :
    Nat.ldiff (segLoopSCK c lo Wm1 n seg start fuel) acc
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n acc start fuel) := by
  induction fuel generalizing acc with
  | zero => rfl
  | succ m ih =>
    rw [segLoopSCK_succ, segAccLoopSK_succ]
    cases testBitK c m with
    | false => exact ih
    | true =>
      simp only [segMarkCK_ldiff, segAccK_eq, ldiff_ldiff, ih]
      refine congrArg (Nat.ldiff seg) ?_
      rw [segAccLoopSK_zero, segAccLoopSK_zero (acc := acc)]
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_or]
      grind

/-- The same, over the base sieve itself: a whole run clears the window once against the joined
masks of every prime it passes. -/
public theorem segLoopCK_eq_ldiff {s lo Wm1 n seg acc start fuel : Nat} :
    Nat.ldiff (segLoopCK s lo Wm1 n seg start fuel) acc
      = Nat.ldiff seg (segAccLoopK s lo Wm1 n acc start fuel) := by
  induction fuel generalizing acc with
  | zero => rfl
  | succ m ih =>
    rw [segLoopCK_succ, segAccLoopK_succ]
    cases testBitK s (start + m) with
    | false => exact ih
    | true =>
      simp only [segMarkCK_ldiff, segAccK_eq, ldiff_ldiff, ih]
      refine congrArg (Nat.ldiff seg) ?_
      rw [segAccLoopK_zero, segAccLoopK_zero (acc := acc)]
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_or]
      grind

/-- A run of a whole window is the window with every mask removed at once. -/
public theorem segLoopCK_ldiff_total {s lo Wm1 n seg start fuel : Nat} :
    segLoopCK s lo Wm1 n seg start fuel
      = Nat.ldiff seg (segAccLoopK s lo Wm1 n 0 start fuel) := by
  have h := segLoopCK_eq_ldiff (s := s) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg) (acc := 0)
    (start := start) (fuel := fuel)
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  rwa [hz] at h

/-- A slice agreeing with the base sieve on the batch's positions runs the clamped batch the same
way. -/
public theorem segLoopSCK_eq {c s lo Wm1 n seg start len : Nat}
    (h : ∀ i < len, testBitK c i = testBitK s (start + i)) :
    segLoopSCK c lo Wm1 n seg start len = segLoopCK s lo Wm1 n seg start len := by
  induction len with
  | zero => rfl
  | succ m ih =>
    rw [segLoopSCK_succ, segLoopCK_succ, ih fun i hi => h i (by lia), h m (by lia)]

/-! ### From the sorted slices back to the batch's run

The fold over sorted slices assembles the same joined mask that the batch's run removes, provided
every prime of the batch is wider than the window (so each has at most two seeds) and the two
tallies account for every position the slice names. -/

/-- Nothing times something, in the raw form the definitions use. -/
public theorem mulK_zero_left {x : Nat} : Nat.mul 0 x = 0 := Nat.zero_mul x

/-- Once times something, in the raw form the definitions use. -/
public theorem mulK_one_left {x : Nat} : Nat.mul 1 x = x := Nat.one_mul x

/-- A record's seed: the low bit of the strike index picks the progression and the rest counts how
many further doubles to step on by. -/
public theorem entrySeedK_pair {lo start i w : Nat} (hw : w < 8) :
    entrySeedK lo start (8 * i + w)
      = Nat.add
          ((Nat.beq (w.land 1) 0).rec
            (firstLocK (indexK ((valueK (start + i)).mul 7)) lo ((valueK (start + i)).mul 2))
            (firstLocK (indexK ((valueK (start + i)).mul 5)) lo ((valueK (start + i)).mul 2)))
          (Nat.mul (w.shiftRight 1) ((valueK (start + i)).mul 2)) := by
  unfold entrySeedK
  rw [shiftRight1_pair hw, land1_pair hw]
  rfl

/-- The first strike of the first progression of the divisor at position `i` of the batch. -/
public theorem entrySeedK_five {lo start i : Nat} :
    entrySeedK lo start (8 * i + 0)
      = firstLocK (indexK ((valueK (start + i)).mul 5)) lo ((valueK (start + i)).mul 2) := by
  rw [entrySeedK_pair (by lia : (0 : Nat) < 8)]
  have h1 : Nat.shiftRight 0 1 = 0 := rfl
  rw [h1, mulK_zero_left]
  rfl

/-- The first strike of the second progression of the divisor at position `i` of the batch. -/
public theorem entrySeedK_seven {lo start i : Nat} :
    entrySeedK lo start (8 * i + 1)
      = firstLocK (indexK ((valueK (start + i)).mul 7)) lo ((valueK (start + i)).mul 2) := by
  rw [entrySeedK_pair (by lia : (1 : Nat) < 8)]
  have h1 : Nat.shiftRight 1 1 = 0 := rfl
  rw [h1, mulK_zero_left]
  rfl

/-- The second strike of the first progression, a further double along. -/
public theorem entrySeedK_five' {lo start i : Nat} :
    entrySeedK lo start (8 * i + 2)
      = firstLocK (indexK ((valueK (start + i)).mul 5)) lo ((valueK (start + i)).mul 2)
        + (valueK (start + i)).mul 2 := by
  rw [entrySeedK_pair (by lia : (2 : Nat) < 8)]
  have h1 : Nat.shiftRight 2 1 = 1 := rfl
  rw [h1, mulK_one_left]
  rfl

/-- The second strike of the second progression, a further double along. -/
public theorem entrySeedK_seven' {lo start i : Nat} :
    entrySeedK lo start (8 * i + 3)
      = firstLocK (indexK ((valueK (start + i)).mul 7)) lo ((valueK (start + i)).mul 2)
        + (valueK (start + i)).mul 2 := by
  rw [entrySeedK_pair (by lia : (3 : Nat) < 8)]
  have h1 : Nat.shiftRight 3 1 = 1 := rfl
  rw [h1, mulK_one_left]
  rfl

/-- The third strike of the first progression, two further doubles along. -/
public theorem entrySeedK_five4 {lo start i : Nat} :
    entrySeedK lo start (8 * i + 4)
      = firstLocK (indexK ((valueK (start + i)).mul 5)) lo ((valueK (start + i)).mul 2)
        + (valueK (start + i)).mul 4 := by
  rw [entrySeedK_pair (by lia : (4 : Nat) < 8)]
  have h1 : Nat.shiftRight 4 1 = 2 := rfl
  have h2 : Nat.mul 2 ((valueK (start + i)).mul 2) = (valueK (start + i)).mul 4 := by lia
  rw [h1, h2]
  rfl

/-- The third strike of the second progression, two further doubles along. -/
public theorem entrySeedK_seven4 {lo start i : Nat} :
    entrySeedK lo start (8 * i + 5)
      = firstLocK (indexK ((valueK (start + i)).mul 7)) lo ((valueK (start + i)).mul 2)
        + (valueK (start + i)).mul 4 := by
  rw [entrySeedK_pair (by lia : (5 : Nat) < 8)]
  have h1 : Nat.shiftRight 5 1 = 2 := rfl
  have h2 : Nat.mul 2 ((valueK (start + i)).mul 2) = (valueK (start + i)).mul 4 := by lia
  rw [h1, h2]
  rfl

/-- The fourth strike of the first progression, three further doubles along. -/
public theorem entrySeedK_five6 {lo start i : Nat} :
    entrySeedK lo start (8 * i + 6)
      = firstLocK (indexK ((valueK (start + i)).mul 5)) lo ((valueK (start + i)).mul 2)
        + ((valueK (start + i)).mul 2 + (valueK (start + i)).mul 4) := by
  rw [entrySeedK_pair (by lia : (6 : Nat) < 8)]
  have h1 : Nat.shiftRight 6 1 = 3 := rfl
  have h2 : Nat.mul 3 ((valueK (start + i)).mul 2)
      = (valueK (start + i)).mul 2 + (valueK (start + i)).mul 4 := by lia
  rw [h1, h2]
  rfl

/-- The fourth strike of the second progression, three further doubles along. -/
public theorem entrySeedK_seven6 {lo start i : Nat} :
    entrySeedK lo start (8 * i + 7)
      = firstLocK (indexK ((valueK (start + i)).mul 7)) lo ((valueK (start + i)).mul 2)
        + ((valueK (start + i)).mul 2 + (valueK (start + i)).mul 4) := by
  rw [entrySeedK_pair (by lia : (7 : Nat) < 8)]
  have h1 : Nat.shiftRight 7 1 = 3 := rfl
  have h2 : Nat.mul 3 ((valueK (start + i)).mul 2)
      = (valueK (start + i)).mul 2 + (valueK (start + i)).mul 4 := by lia
  rw [h1, h2]
  rfl

/-- A position the slice passes over leaves the joined mask alone. -/
public theorem segAccLoopSK_skip {c lo Wm1 n start len : Nat} (h : testBitK c len = false) :
    segAccLoopSK c lo Wm1 n 0 start (len + 1) = segAccLoopSK c lo Wm1 n 0 start len := by
  rw [segAccLoopSK_succ, h]

/-- A position the slice names joins that prime's mask. -/
public theorem segAccLoopSK_take {c lo Wm1 n start len : Nat} (h : testBitK c len = true) :
    segAccLoopSK c lo Wm1 n 0 start (len + 1)
      = segAccK (segAccLoopSK c lo Wm1 n 0 start len) (valueK (start + len)) lo Wm1 n := by
  rw [segAccLoopSK_succ, h]

/-- Where every prime of the batch is wider than the window, the batch's joined mask holds exactly
the in-window seeds of the primes the slice names. -/
public theorem testBit_segAccLoopSK_wide {c lo Wm1 n start len j : Nat} (hj : j ≤ Wm1)
    (hwide : ∀ i, i < len → Wm1 < valueK (start + i) * 2) :
    (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 2 ∧ testBitK c i = true
        ∧ entrySeedK lo start (8 * i + w) = j := by
  induction len with
  | zero =>
    have hz : segAccLoopSK c lo Wm1 n 0 start 0 = 0 := rfl
    rw [hz]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have ih' := ih fun i hi => hwide i (by lia)
    cases hb : testBitK c len with
    | false =>
      rw [segAccLoopSK_skip hb, ih']
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      have hp : Wm1 < valueK (start + len) * 2 := hwide len (by lia)
      rw [segAccLoopSK_take hb, segAccK_eq, buildMaskCK_wide hp, buildMaskCK_zero,
        Nat.testBit_or, Nat.testBit_or, seedK_testBit hj, seedK_testBit hj]
      have hone : ∀ A : Nat, ((1 : Nat) <<< A).testBit j = true ↔ A = j := by
        intro A
        have hs : (1 : Nat) <<< A = Nat.shiftLeft 1 A := rfl
        rw [hs, testBit_oneShift]
        exact ⟨fun h => (Nat.eq_of_beq_eq_true h).symm, fun h => by rw [h]; exact beq_self⟩
      have hA : ((1 : Nat) <<< firstLocK (indexK ((valueK (start + len)).mul 5)) lo
          ((valueK (start + len)).mul 2)).testBit j = true ↔
          entrySeedK lo start (8 * len +0) = j := by
        rw [entrySeedK_five]
        exact hone _
      have hB : ((1 : Nat) <<< firstLocK (indexK ((valueK (start + len)).mul 7)) lo
          ((valueK (start + len)).mul 2)).testBit j = true ↔
          entrySeedK lo start (8 * len +1) = j := by
        rw [entrySeedK_seven]
        exact hone _
      constructor
      · intro h
        rcases (Bool.or_eq_true ..).mp h with h' | h'
        · rcases (Bool.or_eq_true ..).mp h' with h'' | h''
          · exact ⟨len, by lia, 0, by lia, hb, hA.mp h''⟩
          · exact ⟨len, by lia, 1, by lia, hb, hB.mp h''⟩
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := ih'.mp h'
          exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact (Bool.or_eq_true ..).mpr (Or.inr (ih'.mpr ⟨i, h, w, hw, hc, hs⟩))
        · have hil : i = len := by lia
          rw [hil] at hs
          rcases (by lia : w = 0 ∨ w = 1) with hw0 | hw1
          · rw [hw0] at hs
            exact (Bool.or_eq_true ..).mpr (Or.inl ((Bool.or_eq_true ..).mpr
              (Or.inl (hA.mpr hs))))
          · rw [hw1] at hs
            exact (Bool.or_eq_true ..).mpr (Or.inl ((Bool.or_eq_true ..).mpr
              (Or.inr (hB.mpr hs))))

/-- Where every divisor of the batch has its double inside the window and its quadruple past the
end, the batch's joined mask holds exactly the in-window strikes of the divisors the slice names,
and each has four of them. -/
public theorem testBit_segAccLoopSK_band {c lo Wm1 n start len j : Nat} (hj : j ≤ Wm1) (hn : 1 ≤ n)
    (hband : ∀ i, i < len → valueK (start + i) * 2 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 4) :
    (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 4 ∧ testBitK c i = true
        ∧ entrySeedK lo start (8 * i + w) = j := by
  induction len with
  | zero =>
    have hz : segAccLoopSK c lo Wm1 n 0 start 0 = 0 := rfl
    rw [hz]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have ih' := ih fun i hi => hband i (by lia)
    cases hb : testBitK c len with
    | false =>
      rw [segAccLoopSK_skip hb, ih']
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      obtain ⟨hp2, hp4⟩ := hband len (by lia)
      have hm2 : valueK (start + len) * 2 ≤ Wm1 := hp2
      rw [segAccLoopSK_take hb, segAccK_eq, buildMaskCK_band (by lia) hn, buildMaskCK_one hm2,
        Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft,
        seedK_testBit hj, seedK_testBit hj]
      have hsub : j - valueK (start + len) * 2 ≤ Wm1 := by lia
      rw [Nat.testBit_or, seedK_testBit hsub, seedK_testBit hsub]
      have hdist : ∀ d x y : Bool, (d && (x || y)) = ((d && x) || (d && y)) := by
        intro d x y
        cases d <;> cases x <;> cases y <;> rfl
      rw [hdist]
      have hone : ∀ A x : Nat, ((1 : Nat) <<< A).testBit x = true ↔ A = x := by
        intro A x
        have hs : (1 : Nat) <<< A = Nat.shiftLeft 1 A := rfl
        rw [hs, testBit_oneShift]
        exact ⟨fun h => (Nat.eq_of_beq_eq_true h).symm, fun h => by rw [h]; exact beq_self⟩
      have hmul : (valueK (start + len)).mul 2 = valueK (start + len) * 2 := rfl
      have hstep : ∀ X : Nat, (decide (j ≥ valueK (start + len) * 2) &&
          ((1 : Nat) <<< X).testBit (j - valueK (start + len) * 2)) = true ↔
          X + (valueK (start + len)).mul 2 = j := by
        intro X
        constructor
        · intro h
          obtain ⟨hd, hb2⟩ := (Bool.and_eq_true ..).mp h
          have hge : valueK (start + len) * 2 ≤ j := of_decide_eq_true hd
          have hx := (hone X _).mp hb2
          lia
        · intro h
          exact (Bool.and_eq_true ..).mpr
            ⟨decide_eq_true (by lia), (hone X _).mpr (by lia)⟩
      have hA : ((1 : Nat) <<< firstLocK (indexK ((valueK (start + len)).mul 5)) lo
          ((valueK (start + len)).mul 2)).testBit j = true ↔
          entrySeedK lo start (8 * len +0) = j := by
        rw [entrySeedK_five]
        exact hone _ _
      have hB : ((1 : Nat) <<< firstLocK (indexK ((valueK (start + len)).mul 7)) lo
          ((valueK (start + len)).mul 2)).testBit j = true ↔
          entrySeedK lo start (8 * len +1) = j := by
        rw [entrySeedK_seven]
        exact hone _ _
      have hA2 : (decide (j ≥ valueK (start + len) * 2) &&
          ((1 : Nat) <<< firstLocK (indexK ((valueK (start + len)).mul 5)) lo
            ((valueK (start + len)).mul 2)).testBit
              (j - valueK (start + len) * 2)) = true ↔
          entrySeedK lo start (8 * len +2) = j := by
        rw [entrySeedK_five']
        exact hstep _
      have hB2 : (decide (j ≥ valueK (start + len) * 2) &&
          ((1 : Nat) <<< firstLocK (indexK ((valueK (start + len)).mul 7)) lo
            ((valueK (start + len)).mul 2)).testBit
              (j - valueK (start + len) * 2)) = true ↔
          entrySeedK lo start (8 * len +3) = j := by
        rw [entrySeedK_seven']
        exact hstep _
      constructor
      · intro h
        rcases (Bool.or_eq_true ..).mp h with h' | h'
        · rcases (Bool.or_eq_true ..).mp h' with h'' | h''
          · rcases (Bool.or_eq_true ..).mp h'' with h3 | h3
            · exact ⟨len, by lia, 0, by lia, hb, hA.mp h3⟩
            · exact ⟨len, by lia, 1, by lia, hb, hB.mp h3⟩
          · rcases (Bool.or_eq_true ..).mp h'' with h3 | h3
            · exact ⟨len, by lia, 2, by lia, hb, hA2.mp h3⟩
            · exact ⟨len, by lia, 3, by lia, hb, hB2.mp h3⟩
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := ih'.mp h'
          exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact (Bool.or_eq_true ..).mpr (Or.inr (ih'.mpr ⟨i, h, w, hw, hc, hs⟩))
        · have hil : i = len := by lia
          rw [hil] at hs
          refine (Bool.or_eq_true ..).mpr (Or.inl ?_)
          rcases (by lia : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with hw0 | hw1 | hw2 | hw3
          · rw [hw0] at hs
            exact (Bool.or_eq_true ..).mpr (Or.inl ((Bool.or_eq_true ..).mpr (Or.inl (hA.mpr hs))))
          · rw [hw1] at hs
            exact (Bool.or_eq_true ..).mpr (Or.inl ((Bool.or_eq_true ..).mpr (Or.inr (hB.mpr hs))))
          · rw [hw2] at hs
            exact (Bool.or_eq_true ..).mpr (Or.inr ((Bool.or_eq_true ..).mpr (Or.inl (hA2.mpr hs))))
          · rw [hw3] at hs
            exact (Bool.or_eq_true ..).mpr (Or.inr ((Bool.or_eq_true ..).mpr (Or.inr (hB2.mpr hs))))

/-- A single set bit is set exactly at its own place. -/
theorem oneShift_testBit {A x : Nat} : ((1 : Nat) <<< A).testBit x = true ↔ A = x := by
  have hs : (1 : Nat) <<< A = Nat.shiftLeft 1 A := rfl
  rw [hs, testBit_oneShift]
  exact ⟨fun h => (Nat.eq_of_beq_eq_true h).symm, fun h => by rw [h]; exact Nat.beq_eq.mpr rfl⟩

/-- Two clamped seeds hold exactly their own two places, below the window's top. -/
theorem testBit_seedPair {A B M j : Nat} (hj : j ≤ M) :
    (seedK A M ||| seedK B M).testBit j = true ↔ (A = j ∨ B = j) := by
  rw [Nat.testBit_or, seedK_testBit hj, seedK_testBit hj, Bool.or_eq_true]
  exact or_congr oneShift_testBit oneShift_testBit

/-- A seed pair joined with itself a stride along holds four places. -/
theorem testBit_seedQuad {A B M j d : Nat} (hj : j ≤ M) :
    ((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< d).testBit j = true ↔
      (A = j ∨ B = j ∨ A + d = j ∨ B + d = j) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
    testBit_seedPair hj]
  constructor
  · rintro (h | ⟨hd, h2⟩)
    · exact h.imp id Or.inl
    · have hge : d ≤ j := of_decide_eq_true hd
      rcases (testBit_seedPair (M := M) (A := A) (B := B) (j := j - d) (by lia)).mp h2 with h | h
      · exact Or.inr (Or.inr (Or.inl (by lia)))
      · exact Or.inr (Or.inr (Or.inr (by lia)))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨decide_eq_true (by lia),
        (testBit_seedPair (M := M) (A := A) (B := B) (j := j - d) (by lia)).mpr (Or.inl (by lia))⟩
    · exact Or.inr ⟨decide_eq_true (by lia),
        (testBit_seedPair (M := M) (A := A) (B := B) (j := j - d) (by lia)).mpr (Or.inr (by lia))⟩

/-- That four-place mask joined with itself a second stride along holds eight places. -/
theorem testBit_seedOct {A B M j d e : Nat} (hj : j ≤ M) :
    (((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< d)
        ||| ((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< d) <<< e).testBit j
          = true ↔
      (A = j ∨ B = j ∨ A + d = j ∨ B + d = j
        ∨ A + e = j ∨ B + e = j ∨ A + d + e = j ∨ B + d + e = j) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
    testBit_seedQuad hj]
  constructor
  · rintro (h | ⟨hd, h2⟩)
    · exact h.imp id (Or.imp id (Or.imp id Or.inl))
    · have hge : e ≤ j := of_decide_eq_true hd
      rcases (testBit_seedQuad (M := M) (A := A) (B := B) (d := d) (j := j - e) (by lia)).mp h2
        with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by lia)))))))
  · rintro (h | h | h | h | h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr ⟨decide_eq_true (by lia),
        (testBit_seedQuad (M := M) (A := A) (B := B) (d := d) (j := j - e) (by lia)).mpr
          (Or.inl (by lia))⟩
    · exact Or.inr ⟨decide_eq_true (by lia),
        (testBit_seedQuad (M := M) (A := A) (B := B) (d := d) (j := j - e) (by lia)).mpr
          (Or.inr (Or.inl (by lia)))⟩
    · exact Or.inr ⟨decide_eq_true (by lia),
        (testBit_seedQuad (M := M) (A := A) (B := B) (d := d) (j := j - e) (by lia)).mpr
          (Or.inr (Or.inr (Or.inl (by lia))))⟩
    · exact Or.inr ⟨decide_eq_true (by lia),
        (testBit_seedQuad (M := M) (A := A) (B := B) (d := d) (j := j - e) (by lia)).mpr
          (Or.inr (Or.inr (Or.inr (by lia))))⟩

/-- The octave below: the eight-strike mask joined with itself an octuple along holds sixteen
strikes. Doubling `testBit_seedOct` exactly as that doubles `testBit_seedQuad`. -/
theorem testBit_seed16 {A B M j d e f : Nat} (hj : j ≤ M) :
    ((((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< d)
        ||| ((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< d) <<< e)
      ||| (((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< d)
        ||| ((seedK A M ||| seedK B M) ||| (seedK A M ||| seedK B M) <<< d) <<< e)
          <<< f).testBit j = true ↔
      (A = j ∨ B = j ∨ A + d = j ∨ B + d = j
        ∨ A + e = j ∨ B + e = j ∨ A + d + e = j ∨ B + d + e = j
        ∨ A + f = j ∨ B + f = j ∨ A + d + f = j ∨ B + d + f = j
        ∨ A + e + f = j ∨ B + e + f = j ∨ A + d + e + f = j ∨ B + d + e + f = j) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
    testBit_seedOct hj]
  -- The rewrite above has already turned the unshifted half into its disjunction, so only the
  -- shifted half needs the lemma again, and it is named once per branch rather than re-elaborated
  -- per case: `first` across sixteen cases pays for this expression twice a case, which is what
  -- timed this proof out when it was written that way.
  constructor
  · rintro (h | ⟨hd, h2⟩)
    · exact h.imp id (Or.imp id (Or.imp id (Or.imp id (Or.imp id (Or.imp id
        (Or.imp id Or.inl))))))
    · have hge : f ≤ j := of_decide_eq_true hd
      have hhigh := testBit_seedOct (M := M) (A := A) (B := B) (d := d) (e := e) (j := j - f)
        (by lia)
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))))
      rcases hhigh.mp h2 with h | h | h | h | h | h | h | h
      · exact Or.inl (by lia)
      · exact Or.inr (Or.inl (by lia))
      · exact Or.inr (Or.inr (Or.inl (by lia)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by lia))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by lia)))))))
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    all_goals
      refine Or.inr ⟨decide_eq_true (by lia), ?_⟩
    all_goals
      have hhigh := testBit_seedOct (M := M) (A := A) (B := B) (d := d) (e := e) (j := j - f)
        (by lia)
      refine hhigh.mpr ?_
    · exact Or.inl (by lia)
    · exact Or.inr (Or.inl (by lia))
    · exact Or.inr (Or.inr (Or.inl (by lia)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by lia))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by lia)))))))

/-! `entrySeedLK_lane` at a four-bit lane, split by parity. The `Bool.rec` on the lane's low bit
does not reduce for `lia` even when the lane is a literal, so the branch is taken here instead and
a band proof names the parity at the call. Two lemmas rather than one per lane. -/

/-- An even lane names the first progression. -/
public theorem entrySeedLK_lane4_even {lo start i w : Nat} (hw : w < 16) (he : w % 2 = 0) :
    entrySeedLK 4 lo start (16 * i + w)
      = Nat.add (firstLocK (indexK ((valueK (start + i)).mul 5)) lo ((valueK (start + i)).mul 2))
          (Nat.mul (w / 2) ((valueK (start + i)).mul 2)) := by
  -- `exact`, not `rw`: `2 ^ 4 * i + w` is the same term as `16 * i + w` but not the same syntax,
  -- so a rewrite does not find it.
  have h := entrySeedLK_lane (lw := 4) (lo := lo) (start := start) (i := i) (w := w) hw
  rw [he] at h
  exact h

/-- An odd lane names the second. -/
public theorem entrySeedLK_lane4_odd {lo start i w : Nat} (hw : w < 16) (ho : w % 2 = 1) :
    entrySeedLK 4 lo start (16 * i + w)
      = Nat.add (firstLocK (indexK ((valueK (start + i)).mul 7)) lo ((valueK (start + i)).mul 2))
          (Nat.mul (w / 2) ((valueK (start + i)).mul 2)) := by
  have h := entrySeedLK_lane (lw := 4) (lo := lo) (start := start) (i := i) (w := w) hw
  rw [ho] at h
  exact h

/-- The octave below `testBit_segAccLoopSK_band8`: every divisor of the batch has its octuple
inside the window and its sixteenfold past the end, so each has sixteen strikes and the batch's
joined mask holds exactly the in-window ones of the divisors the slice names. -/
public theorem testBit_segAccLoopSK_band16 {c lo Wm1 n start len j : Nat} (hj : j ≤ Wm1)
    (hn : 3 ≤ n)
    (hband : ∀ i, i < len → valueK (start + i) * 8 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 16) :
    (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 16 ∧ testBitK c i = true
        ∧ entrySeedLK 4 lo start (16 * i + w) = j := by
  induction len with
  | zero =>
    have hz : segAccLoopSK c lo Wm1 n 0 start 0 = 0 := rfl
    rw [hz]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have ih' := ih fun i hi => hband i (by lia)
    cases hb : testBitK c len with
    | false =>
      rw [segAccLoopSK_skip hb, ih']
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      obtain ⟨hp8, hp16⟩ := hband len (by lia)
      have hm2 : valueK (start + len) * 2 ≤ Wm1 := by lia
      have hm4 : valueK (start + len) * 4 ≤ Wm1 := by lia
      rw [segAccLoopSK_take hb, segAccK_eq, buildMaskCK_hexa hp16 hn, buildMaskCK_three hp8,
        buildMaskCK_two hm2 hm4, Nat.testBit_or, Bool.or_eq_true, testBit_seed16 hj, ih']
      constructor
      · rintro ((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | h)
        · exact ⟨len, by lia, 0, by lia, hb, by rw [entrySeedLK_lane4_even (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 1, by lia, hb, by rw [entrySeedLK_lane4_odd (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 2, by lia, hb, by rw [entrySeedLK_lane4_even (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 3, by lia, hb, by rw [entrySeedLK_lane4_odd (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 4, by lia, hb, by rw [entrySeedLK_lane4_even (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 5, by lia, hb, by rw [entrySeedLK_lane4_odd (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 6, by lia, hb, by rw [entrySeedLK_lane4_even (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 7, by lia, hb, by rw [entrySeedLK_lane4_odd (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 8, by lia, hb, by rw [entrySeedLK_lane4_even (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 9, by lia, hb, by rw [entrySeedLK_lane4_odd (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 10, by lia, hb,
            by rw [entrySeedLK_lane4_even (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 11, by lia, hb,
            by rw [entrySeedLK_lane4_odd (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 12, by lia, hb,
            by rw [entrySeedLK_lane4_even (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 13, by lia, hb,
            by rw [entrySeedLK_lane4_odd (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 14, by lia, hb,
            by rw [entrySeedLK_lane4_even (by lia) (by lia)]; lia⟩
        · exact ⟨len, by lia, 15, by lia, hb,
            by rw [entrySeedLK_lane4_odd (by lia) (by lia)]; lia⟩
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := h
          exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact Or.inr ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil] at hs
          refine Or.inl ?_
          rcases (by lia : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7
            ∨ w = 8 ∨ w = 9 ∨ w = 10 ∨ w = 11 ∨ w = 12 ∨ w = 13 ∨ w = 14 ∨ w = 15)
            with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
          · rw [h0, entrySeedLK_lane4_even (by lia) (by lia)] at hs
            exact Or.inl (by lia)
          · rw [h1, entrySeedLK_lane4_odd (by lia) (by lia)] at hs
            exact Or.inr (Or.inl (by lia))
          · rw [h2, entrySeedLK_lane4_even (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inl (by lia)))
          · rw [h3, entrySeedLK_lane4_odd (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inl (by lia))))
          · rw [h4, entrySeedLK_lane4_even (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))
          · rw [h5, entrySeedLK_lane4_odd (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia))))))
          · rw [h6, entrySeedLK_lane4_even (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))))
          · rw [h7, entrySeedLK_lane4_odd (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia))))))))
          · rw [h8, entrySeedLK_lane4_even (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl (by lia)))))))))
          · rw [h9, entrySeedLK_lane4_odd (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl (by lia))))))))))
          · rw [h10, entrySeedLK_lane4_even (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl (by lia)))))))))))
          · rw [h11, entrySeedLK_lane4_odd (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl (by lia))))))))))))
          · rw [h12, entrySeedLK_lane4_even (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inl (by lia)))))))))))))
          · rw [h13, entrySeedLK_lane4_odd (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inl (by lia))))))))))))))
          · rw [h14, entrySeedLK_lane4_even (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))))))))))))
          · rw [h15, entrySeedLK_lane4_odd (by lia) (by lia)] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by lia)))))))))))))))

/-- Where every divisor of the batch has its quadruple inside the window and its octuple past the
end, the batch's joined mask holds exactly the in-window strikes of the divisors the slice names,
and each has eight of them. -/
public theorem testBit_segAccLoopSK_band8 {c lo Wm1 n start len j : Nat} (hj : j ≤ Wm1)
    (hn : 2 ≤ n)
    (hband : ∀ i, i < len → valueK (start + i) * 4 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 8) :
    (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 8 ∧ testBitK c i = true
        ∧ entrySeedK lo start (8 * i + w) = j := by
  induction len with
  | zero =>
    have hz : segAccLoopSK c lo Wm1 n 0 start 0 = 0 := rfl
    rw [hz]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have ih' := ih fun i hi => hband i (by lia)
    cases hb : testBitK c len with
    | false =>
      rw [segAccLoopSK_skip hb, ih']
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      obtain ⟨hp4, hp8⟩ := hband len (by lia)
      have hm2 : valueK (start + len) * 2 ≤ Wm1 := by lia
      rw [segAccLoopSK_take hb, segAccK_eq, buildMaskCK_octave hp8 hn, buildMaskCK_two hm2 hp4,
        Nat.testBit_or, Bool.or_eq_true, testBit_seedOct hj, ih']
      constructor
      · rintro ((h | h | h | h | h | h | h | h) | h)
        · exact ⟨len, by lia, 0, by lia, hb, by rw [entrySeedK_five]; lia⟩
        · exact ⟨len, by lia, 1, by lia, hb, by rw [entrySeedK_seven]; lia⟩
        · exact ⟨len, by lia, 2, by lia, hb, by rw [entrySeedK_five']; lia⟩
        · exact ⟨len, by lia, 3, by lia, hb, by rw [entrySeedK_seven']; lia⟩
        · exact ⟨len, by lia, 4, by lia, hb, by rw [entrySeedK_five4]; lia⟩
        · exact ⟨len, by lia, 5, by lia, hb, by rw [entrySeedK_seven4]; lia⟩
        · exact ⟨len, by lia, 6, by lia, hb, by rw [entrySeedK_five6]; lia⟩
        · exact ⟨len, by lia, 7, by lia, hb, by rw [entrySeedK_seven6]; lia⟩
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := h
          exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact Or.inr ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil] at hs
          refine Or.inl ?_
          rcases (by lia : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7)
            with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
          · rw [h0, entrySeedK_five] at hs
            exact Or.inl (by lia)
          · rw [h1, entrySeedK_seven] at hs
            exact Or.inr (Or.inl (by lia))
          · rw [h2, entrySeedK_five'] at hs
            exact Or.inr (Or.inr (Or.inl (by lia)))
          · rw [h3, entrySeedK_seven'] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inl (by lia))))
          · rw [h4, entrySeedK_five4] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))
          · rw [h5, entrySeedK_seven4] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia))))))
          · rw [h6, entrySeedK_five6] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by lia)))))))
          · rw [h7, entrySeedK_seven6] at hs
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by lia)))))))

/-- The tally a completed batch carries is the batch's own slice, once per progression, so one
equation above the window settles every position at once. -/
public theorem tally_of_shiftRight {c lo start len W Wm1 slotW Ls Cs np : Nat}
    (h : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W = c ||| c <<< len) :
    ∀ i, i < len → ∀ w, w < 2 → testBitK c i = true →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = true := by
  intro i hi w hw hc
  have hcb : c.testBit i = true := by rw [← testBitK_eq_testBit]; exact hc
  have hsr : ((stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W).testBit (i + w * len)
      = (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) := by
    have hx : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
        = stripeBatchK c lo start len W Wm1 slotW Ls Cs np >>> W := rfl
    rw [hx, Nat.testBit_shiftRight]
  rw [← hsr, h, Nat.testBit_or]
  rcases (by lia : w = 0 ∨ w = 1) with hw0 | hw1
  · rw [hw0]
    simp [hcb]
  · rw [hw1, Nat.testBit_shiftLeft]
    simp [hcb]

/-- The same equation says the tally is silent about the two strikes a further double along, which
is what tells a reader of a finished batch that no record claimed one. -/
public theorem tally_clear_of_shiftRight {c lo start len W Wm1 slotW Ls Cs np : Nat}
    (hc2 : c < 2 ^ len)
    (h : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W = c ||| c <<< len) :
    ∀ i, ∀ w, 2 ≤ w → w < 8 →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = false := by
  intro i w hw2 hw4
  have hsr : ((stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W).testBit (i + w * len)
      = (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) := by
    have hx : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
        = stripeBatchK c lo start len W Wm1 slotW Ls Cs np >>> W := rfl
    rw [hx, Nat.testBit_shiftRight]
  rw [← hsr, h, Nat.testBit_or, Nat.testBit_shiftLeft]
  have hmul : 2 * len ≤ w * len := Nat.mul_le_mul_right len hw2
  have hlo : c.testBit (i + w * len) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc2 (Nat.pow_le_pow_right (by lia) (by lia)))
  have hhi : c.testBit (i + w * len - len) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc2 (Nat.pow_le_pow_right (by lia) (by lia)))
  simp [hlo, hhi]

/-- Over a batch of primes each wider than the window, and given tallies that account for both
progressions of every position the batch's slice names, the fold over sorted slices removes from
the window exactly what the batch's run removes. -/
public theorem segLoopSCK_eq_stripe {c lo start len n W Wm1 slotW Ls Cs np seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hc2 : c < 2 ^ len) (hW : np * 65536 ≤ W) (hWm1 : Wm1 < W)
    (hwide : ∀ i, i < len → Wm1 < valueK (start + i) * 2)
    (htal : ∀ i, i < len → ∀ w, w < 2 → testBitK c i = true →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = true)
    (hnot : ∀ i, ∀ w, 2 ≤ w → w < 8 →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = false) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (stripeBatchK c lo start len W Wm1 slotW Ls Cs np) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit j = true := by
      constructor
      · intro h
        obtain ⟨i, hi, w, hw, hc, hsd⟩ := (testBit_segAccLoopSK_wide hj hwide).mp h
        have hX : entrySeedK lo start (8 * i + w) ≤ Wm1 := by rw [hsd]; exact hj
        have := stripeBatchK_complete (c := c) (lo := lo) (start := start) (len := len) (W := W)
          (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hc2 hi hW hWm1
          (htal i hi w hw hc) hX
        rwa [hsd] at this
      · intro h
        obtain ⟨k, m, hk, hm, hcbit, hk16, hsd⟩ :=
          (testBit_stripeBatchK_eq (by lia : j < W)).mp h
        -- a record naming a strike a further double along would show in the tally, which the
        -- batch's own equation says is silent there
        have hw2 : (entryOf Ls slotW k m).land 7 < 2 := by
          by_contra hge
          have hset := testBit_stripeBatchK_tally (len := len) (Wm1 := Wm1) hW hk hm hcbit hk16
          rw [hnot _ _ (by lia) land_one_lt] at hset
          simp at hset
        refine (testBit_segAccLoopSK_wide hj hwide).mpr
          ⟨(entryOf Ls slotW k m).shiftRight 3, ?_, (entryOf Ls slotW k m).land 7,
            hw2, hcbit, ?_⟩
        · by_contra hge
          rw [testBitK_of_lt hc2 (by lia)] at hcbit
          simp at hcbit
        · rw [entry_split]
          exact hsd
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

/-! ### The tally, folded, so a band of any width needs no case per lane

`tally_of_shiftRight` and the two below it split into as many cases as the band has lanes, which is
fine at two, four and eight and tiresome at sixteen. Folding the tally lets the same fact be proved
once by induction on the lane count. -/

/-- The tally a complete batch carries: the batch's own slice once per lane. -/
@[expose] public noncomputable def tallyUpToK (c len n : Nat) : Nat :=
  n.rec 0 fun w acc => acc.lor (c.shiftLeft (w.mul len))

/-- Every lane of every position the batch names is set in the folded tally. -/
public theorem testBit_tallyUpToK {c len n i w : Nat} (hw : w < n)
    (hc : c.testBit i = true) : (tallyUpToK c len n).testBit (i + w * len) = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hstep : tallyUpToK c len (n + 1)
        = (tallyUpToK c len n).lor (c.shiftLeft (n.mul len)) := rfl
    have hlor : ∀ a b : Nat, a.lor b = a ||| b := fun _ _ => rfl
    rw [hstep, hlor, Nat.testBit_or]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hlt | heq
    · rw [ih hlt, Bool.true_or]
    · subst heq
      have hsl : c.shiftLeft (w.mul len) = c <<< (w * len) := rfl
      rw [hsl, Nat.testBit_shiftLeft]
      simp [hc]

/-- What the per-lane tally lemmas say, for any lane count and without a case per lane. -/
public theorem tallyN_of_shiftRight {X c len W n : Nat}
    (h : X.shiftRight W = tallyUpToK c len n) :
    ∀ i, i < len → ∀ w, w < n → testBitK c i = true →
      X.testBit (W + (i + w * len)) = true := by
  intro i _ w hw hc
  have hcb : c.testBit i = true := by rw [← testBitK_eq_testBit]; exact hc
  have hsr : (X.shiftRight W).testBit (i + w * len) = X.testBit (W + (i + w * len)) := by
    have hx : X.shiftRight W = X >>> W := rfl
    rw [hx, Nat.testBit_shiftRight]
  rw [← hsr, h]
  exact testBit_tallyUpToK hw hcb

/-- Where a divisor has four strikes, the tally a finished batch carries is its own slice once per
strike, so again one equation above the window settles every position. -/
public theorem tally4_of_shiftRight {c lo start len W Wm1 slotW Ls Cs np : Nat}
    (h : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
      = ((c ||| c <<< len) ||| c <<< (2 * len)) ||| c <<< (3 * len)) :
    ∀ i, i < len → ∀ w, w < 4 → testBitK c i = true →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = true := by
  intro i hi w hw hc
  have hcb : c.testBit i = true := by rw [← testBitK_eq_testBit]; exact hc
  have hsr : ((stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W).testBit (i + w * len)
      = (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) := by
    have hx : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
        = stripeBatchK c lo start len W Wm1 slotW Ls Cs np >>> W := rfl
    rw [hx, Nat.testBit_shiftRight]
  rw [← hsr, h, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
  rcases (by lia : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with hw0 | hw1 | hw2 | hw3
  · rw [hw0]
    simp [hcb]
  · rw [hw1, Nat.testBit_shiftLeft]
    simp [hcb]
  · rw [hw2, Nat.testBit_shiftLeft]
    simp [hcb]
  · rw [hw3, Nat.testBit_shiftLeft]
    simp [hcb]

/-- The same equation says the tally is silent about the four strikes beyond a divisor's four. -/
public theorem tally4_clear_of_shiftRight {c lo start len W Wm1 slotW Ls Cs np : Nat}
    (hc2 : c < 2 ^ len)
    (h : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
      = ((c ||| c <<< len) ||| c <<< (2 * len)) ||| c <<< (3 * len)) :
    ∀ i, ∀ w, 4 ≤ w → w < 8 →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = false := by
  intro i w hw4 hw8
  have hsr : ((stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W).testBit (i + w * len)
      = (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) := by
    have hx : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
        = stripeBatchK c lo start len W Wm1 slotW Ls Cs np >>> W := rfl
    rw [hx, Nat.testBit_shiftRight]
  rw [← hsr, h, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  have hmul : 4 * len ≤ w * len := Nat.mul_le_mul_right len hw4
  have h0 : c.testBit (i + w * len) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc2 (Nat.pow_le_pow_right (by lia) (by lia)))
  have h1 : c.testBit (i + w * len - len) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc2 (Nat.pow_le_pow_right (by lia) (by lia)))
  have h2 : c.testBit (i + w * len - 2 * len) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc2 (Nat.pow_le_pow_right (by lia) (by lia)))
  have h3 : c.testBit (i + w * len - 3 * len) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc2 (Nat.pow_le_pow_right (by lia) (by lia)))
  simp [h0, h1, h2, h3]

/-- Where a divisor has eight strikes, the tally a finished batch carries is its own slice once per
strike, so again one equation above the window settles every position. -/
public theorem tally8_of_shiftRight {c lo start len W Wm1 slotW Ls Cs np : Nat}
    (h : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
      = ((((((c ||| c <<< len) ||| c <<< (2 * len)) ||| c <<< (3 * len)) ||| c <<< (4 * len))
        ||| c <<< (5 * len)) ||| c <<< (6 * len)) ||| c <<< (7 * len)) :
    ∀ i, i < len → ∀ w, w < 8 → testBitK c i = true →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = true := by
  intro i hi w hw hc
  have hcb : c.testBit i = true := by rw [← testBitK_eq_testBit]; exact hc
  have hsr : ((stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W).testBit (i + w * len)
      = (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) := by
    have hx : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
        = stripeBatchK c lo start len W Wm1 slotW Ls Cs np >>> W := rfl
    rw [hx, Nat.testBit_shiftRight]
  rw [← hsr, h, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or,
    Nat.testBit_or, Nat.testBit_or]
  rcases (by lia : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7)
    with hw0 | hw1 | hw2 | hw3 | hw4 | hw5 | hw6 | hw7
  · rw [hw0]
    simp [hcb]
  · rw [hw1, Nat.testBit_shiftLeft]
    simp [hcb]
  · rw [hw2, Nat.testBit_shiftLeft]
    simp [hcb]
  · rw [hw3, Nat.testBit_shiftLeft]
    simp [hcb]
  · rw [hw4, Nat.testBit_shiftLeft]
    simp [hcb]
  · rw [hw5, Nat.testBit_shiftLeft]
    simp [hcb]
  · rw [hw6, Nat.testBit_shiftLeft]
    simp [hcb]
  · rw [hw7, Nat.testBit_shiftLeft]
    simp [hcb]

/-- The same for a batch of divisors whose doubles fit the window and whose quadruples pass its
end, where each has four strikes rather than two and the tally accounts for all four. -/
public theorem segLoopSCK_eq_stripe_band {c lo start len n W Wm1 slotW Ls Cs np seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hc2 : c < 2 ^ len) (hW : np * 65536 ≤ W) (hWm1 : Wm1 < W)
    (hn : 1 ≤ n)
    (hband : ∀ i, i < len → valueK (start + i) * 2 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 4)
    (htal : ∀ i, i < len → ∀ w, w < 4 → testBitK c i = true →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = true)
    (hnot : ∀ i, ∀ w, 4 ≤ w → w < 8 →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = false) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (stripeBatchK c lo start len W Wm1 slotW Ls Cs np) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit j = true := by
      constructor
      · intro h
        obtain ⟨i, hi, w, hw, hc, hsd⟩ := (testBit_segAccLoopSK_band hj hn hband).mp h
        have hX : entrySeedK lo start (8 * i + w) ≤ Wm1 := by rw [hsd]; exact hj
        have := stripeBatchK_complete (c := c) (lo := lo) (start := start) (len := len) (W := W)
          (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hc2 hi hW hWm1
          (htal i hi w hw hc) hX
        rwa [hsd] at this
      · intro h
        obtain ⟨k, m, hk, hm, hcbit, hk16, hsd⟩ :=
          (testBit_stripeBatchK_eq (by lia : j < W)).mp h
        -- a record naming a strike three or four doubles along would show in the tally, which the
        -- batch's own equation says is silent there
        have hw4 : (entryOf Ls slotW k m).land 7 < 4 := by
          by_contra hge
          have hset := testBit_stripeBatchK_tally (len := len) (Wm1 := Wm1) hW hk hm hcbit hk16
          rw [hnot _ _ (by lia) land_one_lt] at hset
          simp at hset
        refine (testBit_segAccLoopSK_band hj hn hband).mpr
          ⟨(entryOf Ls slotW k m).shiftRight 3, ?_, (entryOf Ls slotW k m).land 7,
            hw4, hcbit, ?_⟩
        · by_contra hge
          rw [testBitK_of_lt hc2 (by lia)] at hcbit
          simp at hcbit
        · rw [entry_split]
          exact hsd
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

/-- The same for a batch of divisors whose quadruples fit the window and whose octuples pass its
end, where each has eight strikes. Every record a batch carries names one of the eight, so unlike
the four-strike band there is nothing for the tally to be silent about. -/
public theorem segLoopSCK_eq_stripe_band8 {c lo start len n W Wm1 slotW Ls Cs np seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hc2 : c < 2 ^ len) (hW : np * 65536 ≤ W) (hWm1 : Wm1 < W)
    (hn : 2 ≤ n)
    (hband : ∀ i, i < len → valueK (start + i) * 4 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 8)
    (htal : ∀ i, i < len → ∀ w, w < 8 → testBitK c i = true →
      (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit (W + (i + w * len)) = true) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (stripeBatchK c lo start len W Wm1 slotW Ls Cs np) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit j = true := by
      constructor
      · intro h
        obtain ⟨i, hi, w, hw, hc, hsd⟩ := (testBit_segAccLoopSK_band8 hj hn hband).mp h
        have hX : entrySeedK lo start (8 * i + w) ≤ Wm1 := by rw [hsd]; exact hj
        have := stripeBatchK_complete (c := c) (lo := lo) (start := start) (len := len) (W := W)
          (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hc2 hi hW hWm1
          (htal i hi w hw hc) hX
        rwa [hsd] at this
      · intro h
        obtain ⟨k, m, hk, hm, hcbit, hk16, hsd⟩ :=
          (testBit_stripeBatchK_eq (by lia : j < W)).mp h
        refine (testBit_segAccLoopSK_band8 hj hn hband).mpr
          ⟨(entryOf Ls slotW k m).shiftRight 3, ?_, (entryOf Ls slotW k m).land 7,
            land_one_lt, hcbit, ?_⟩
        · by_contra hge
          rw [testBitK_of_lt hc2 (by lia)] at hcbit
          simp at hcbit
        · rw [entry_split]
          exact hsd
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

/-- Nothing above the batch's positions means below the batch's width. -/
public theorem lt_two_pow_of_shiftRight {c len : Nat} (h : c.shiftRight len = 0) : c < 2 ^ len := by
  have h1 : c.shiftRight len = c / 2 ^ len := by
    have hx : c.shiftRight len = c >>> len := rfl
    rw [hx, Nat.shiftRight_eq_div_pow]
  rw [h1] at h
  exact Nat.lt_of_div_eq_zero (Nat.two_pow_pos len) h

/-- One test settles the whole batch: if the batch's first prime is wider than the window, so is
every later one. -/
public theorem wide_of_blt {Wm1 start len : Nat}
    (h : Nat.blt Wm1 (Nat.mul (valueK start) 2) = true) :
    ∀ i, i < len → Wm1 < valueK (start + i) * 2 := by
  intro i _
  have hb : Nat.ble (Wm1 + 1) (Nat.mul (valueK start) 2) = true := h
  have h1 : Wm1 + 1 ≤ valueK start * 2 := Nat.le_of_ble_eq_true hb
  have h2 : valueK start ≤ valueK (start + i) := valueK_le (by lia)
  lia

/-- Two tests settle the whole batch: the last divisor's double still fits the window, and the
first divisor's quadruple already passes its end. -/
public theorem band_of_tests {Wm1 start len : Nat}
    (hlast : Nat.ble (Nat.mul (valueK (start + len)) 2) Wm1 = true)
    (hfirst : Nat.blt Wm1 (Nat.mul (valueK start) 4) = true) :
    ∀ i, i < len → valueK (start + i) * 2 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 4 := by
  intro i hi
  have h1 : valueK (start + len) * 2 ≤ Wm1 := Nat.le_of_ble_eq_true hlast
  have hb : Nat.ble (Wm1 + 1) (Nat.mul (valueK start) 4) = true := hfirst
  have h2 : Wm1 + 1 ≤ valueK start * 4 := Nat.le_of_ble_eq_true hb
  have h3 : valueK (start + i) ≤ valueK (start + len) := valueK_le (by lia)
  have h4 : valueK start ≤ valueK (start + i) := valueK_le (by lia)
  exact ⟨by lia, by lia⟩

/-- Two tests settle the octave below: the last divisor's quadruple still fits the window, and the
first divisor's octuple already passes its end. -/
public theorem octave_of_tests {Wm1 start len : Nat}
    (hlast : Nat.ble (Nat.mul (valueK (start + len)) 4) Wm1 = true)
    (hfirst : Nat.blt Wm1 (Nat.mul (valueK start) 8) = true) :
    ∀ i, i < len → valueK (start + i) * 4 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 8 := by
  intro i hi
  have h1 : valueK (start + len) * 4 ≤ Wm1 := Nat.le_of_ble_eq_true hlast
  have hb : Nat.ble (Wm1 + 1) (Nat.mul (valueK start) 8) = true := hfirst
  have h2 : Wm1 + 1 ≤ valueK start * 8 := Nat.le_of_ble_eq_true hb
  have h3 : valueK (start + i) ≤ valueK (start + len) := valueK_le (by lia)
  have h4 : valueK start ≤ valueK (start + i) := valueK_le (by lia)
  exact ⟨by lia, by lia⟩

/-- A clear only takes bits away, so the window stays within its width. -/
public theorem sub_lt_two_pow {seg m next Wm1 : Nat} (hseg : seg < 2 ^ (Wm1 + 1))
    (h : Nat.sub seg m = next) : next < 2 ^ (Wm1 + 1) := by
  have hle : next ≤ seg := by
    rw [← h]
    exact Nat.sub_le _ _
  lia

/-- One batch of the sieve run, carried out by sorting its primes into slices of the window. The
window's own width appears twice over: as the place the tally starts, and as the bound the window
sits under, which is why `Wm1 + 1 = W` is one of the tests. -/
public theorem stripeStep {c lo Wm1 n W start len slotW Ls Cs np seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hc0 : Nat.beq (c.shiftRight len) 0 = true) (hW : Nat.ble (Nat.mul np 65536) W = true)
    (hwide : Nat.blt Wm1 (Nat.mul (valueK start) 2) = true)
    (hbatch : Nat.beq (stripeBatchK c lo start len W Wm1 slotW Ls Cs np) lit = true)
    (htally : Nat.beq (lit.shiftRight W) (c ||| c <<< len) = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hW' : np * 65536 ≤ W := Nat.le_of_ble_eq_true hW
  have hWm1' : Wm1 < W := by lia
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hb := Nat.eq_of_beq_eq_true hbatch
  have hsr : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W = c ||| c <<< len := by
    rw [hb]
    exact Nat.eq_of_beq_eq_true htally
  have hc2 := lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hc0)
  have htal := tally_of_shiftRight (c := c) (lo := lo) (start := start) (len := len) (W := W)
    (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hsr
  have hnot := tally_clear_of_shiftRight (c := c) (lo := lo) (start := start) (len := len) (W := W)
    (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hc2 hsr
  refine Nat.beq_eq.mpr ?_
  rw [segLoopSCK_eq_stripe hseg hc2 hW' hWm1' (wide_of_blt hwide) htal hnot, hb, ldiff_eq_sub]
  exact Nat.eq_of_beq_eq_true hclear

/-- One batch of the band whose divisors strike three or four times, carried out by sorting those
strikes into slices, with everything the kernel owes as a Boolean test or an equation. -/
public theorem stripeStepBand {c lo Wm1 n W start len slotW Ls Cs np seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hc0 : Nat.beq (c.shiftRight len) 0 = true) (hW : Nat.ble (Nat.mul np 65536) W = true)
    (hn : Nat.ble 1 n = true)
    (hlast : Nat.ble (Nat.mul (valueK (start + len)) 2) Wm1 = true)
    (hfirst : Nat.blt Wm1 (Nat.mul (valueK start) 4) = true)
    (hbatch : Nat.beq (stripeBatchK c lo start len W Wm1 slotW Ls Cs np) lit = true)
    (htally : Nat.beq (lit.shiftRight W)
      (((c ||| c <<< len) ||| c <<< (2 * len)) ||| c <<< (3 * len)) = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hW' : np * 65536 ≤ W := Nat.le_of_ble_eq_true hW
  have hWm1' : Wm1 < W := by lia
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hb := Nat.eq_of_beq_eq_true hbatch
  have hsr : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
      = ((c ||| c <<< len) ||| c <<< (2 * len)) ||| c <<< (3 * len) := by
    rw [hb]
    exact Nat.eq_of_beq_eq_true htally
  have hc2 := lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hc0)
  have htal := tally4_of_shiftRight (c := c) (lo := lo) (start := start) (len := len) (W := W)
    (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hsr
  have hnot := tally4_clear_of_shiftRight (c := c) (lo := lo) (start := start) (len := len)
    (W := W) (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hc2 hsr
  refine Nat.beq_eq.mpr ?_
  rw [segLoopSCK_eq_stripe_band hseg hc2 hW' hWm1' (Nat.le_of_ble_eq_true hn)
    (band_of_tests hlast hfirst) htal hnot, hb, ldiff_eq_sub]
  exact Nat.eq_of_beq_eq_true hclear

/-- One batch of the octave below, where a divisor strikes up to eight times, carried out by
sorting those strikes into slices. -/
public theorem stripeStepBand8 {c lo Wm1 n W start len slotW Ls Cs np seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hc0 : Nat.beq (c.shiftRight len) 0 = true) (hW : Nat.ble (Nat.mul np 65536) W = true)
    (hn : Nat.ble 2 n = true)
    (hlast : Nat.ble (Nat.mul (valueK (start + len)) 4) Wm1 = true)
    (hfirst : Nat.blt Wm1 (Nat.mul (valueK start) 8) = true)
    (hbatch : Nat.beq (stripeBatchK c lo start len W Wm1 slotW Ls Cs np) lit = true)
    (htally : Nat.beq (lit.shiftRight W)
      (((((((c ||| c <<< len) ||| c <<< (2 * len)) ||| c <<< (3 * len)) ||| c <<< (4 * len))
        ||| c <<< (5 * len)) ||| c <<< (6 * len)) ||| c <<< (7 * len)) = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hW' : np * 65536 ≤ W := Nat.le_of_ble_eq_true hW
  have hWm1' : Wm1 < W := by lia
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hb := Nat.eq_of_beq_eq_true hbatch
  have hsr : (stripeBatchK c lo start len W Wm1 slotW Ls Cs np).shiftRight W
      = ((((((c ||| c <<< len) ||| c <<< (2 * len)) ||| c <<< (3 * len)) ||| c <<< (4 * len))
        ||| c <<< (5 * len)) ||| c <<< (6 * len)) ||| c <<< (7 * len) := by
    rw [hb]
    exact Nat.eq_of_beq_eq_true htally
  have hc2 := lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hc0)
  have htal := tally8_of_shiftRight (c := c) (lo := lo) (start := start) (len := len) (W := W)
    (Wm1 := Wm1) (slotW := slotW) (Ls := Ls) (Cs := Cs) hsr
  refine Nat.beq_eq.mpr ?_
  rw [segLoopSCK_eq_stripe_band8 hseg hc2 hW' hWm1' (Nat.le_of_ble_eq_true hn)
    (octave_of_tests hlast hfirst) htal, hb, ldiff_eq_sub]
  exact Nat.eq_of_beq_eq_true hclear

/-- A clamped run of a whole window gives the value the plain run gives, with the three side
conditions as Boolean tests the kernel settles. -/
public theorem segEq_of_clamped {s lo W Wm1 n fuel b : Nat} (hW : (Wm1 + 1).beq W)
    (hn : Nat.blt Wm1 (2 ^ n)) (hn32 : Nat.ble n 32)
    (h : segLoopCK s lo Wm1 n (initSegK W) 1 fuel = b) :
    segLoopK s lo Wm1 (initSegK W) 1 fuel = b := by
  have hw : Wm1 + 1 = W := by grind [Nat.beq_eq]
  have h1 : initSegK W < 2 ^ (Wm1 + 1) := by rw [hw]; exact initSegK_lt
  have h2 : Wm1 < 2 ^ n := by grind [Nat.blt_eq]
  have h3 : n ≤ 32 := by grind [Nat.ble_eq]
  rw [← segLoopCK_eq h1 h2 h3]
  exact h

/-! ### From a slice of the base sieve back to the base sieve

`segLoopSK` reads a slice, so a batch equation about it says nothing about the base sieve until
the slice is tied back. The two lemmas below do that: a slice agreeing with the base sieve on the
batch's positions gives the same run, and the slice the emitter uses does agree. -/

/-- Loop recurrence for `segLoopSK`. -/
public theorem segLoopSK_succ {c lo Wm1 seg start fuel : Nat} :
    segLoopSK c lo Wm1 seg start (fuel + 1)
      = Bool.rec (segLoopSK c lo Wm1 seg start fuel)
          (segMarkK (segLoopSK c lo Wm1 seg start fuel) (valueK (start + fuel)) lo Wm1)
          (testBitK c fuel) := rfl

/-- A slice that agrees with the base sieve on the batch's positions runs the batch the same way. -/
public theorem segLoopSK_eq {c s lo Wm1 seg start len : Nat}
    (h : ∀ i < len, testBitK c i = testBitK s (start + i)) :
    segLoopSK c lo Wm1 seg start len = segLoopK s lo Wm1 seg start len := by
  induction len with
  | zero => rfl
  | succ n ih =>
    rw [segLoopSK_succ, segLoopK_succ, ih fun i hi => h i (by lia), h n (by lia)]

/-- The slice `(s >>> start) &&& (2 ^ len - 1)` agrees with `s` on the batch's positions. -/
public theorem testBitK_slice {s start len i : Nat} (hi : i < len) :
    testBitK (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)) i
      = testBitK s (start + i) := by
  simp [testBitK_eq_testBit, Nat.shiftLeft_eq, Nat.testBit_shiftRight, hi]

/-- A batch settled with its own round count, restated for the unclamped run. The round count
appears nowhere in the conclusion, so batches with different counts chain together. -/
public theorem segLoopK_batch {s c lo Wm1 n W seg start len next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hn32 : Nat.ble n 32 = true)
    (hstride : Nat.blt Wm1 (Nat.mul (valueK start) (Nat.pow 2 (n + 1))) = true)
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c = true)
    (h : (segLoopSCK c lo Wm1 n seg start len).beq next = true) :
    (segLoopK s lo Wm1 seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hsb : Nat.ble (Wm1 + 1) (Nat.mul (valueK start) (Nat.pow 2 (n + 1))) = true := hstride
  have hst : Wm1 < valueK start * 2 ^ (n + 1) := Nat.le_of_ble_eq_true hsb
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSCK_eq fun i hi => testBitK_slice hi,
    segLoopCK_eq_stride hseg hst (Nat.le_of_ble_eq_true hn32)] at h
  exact h

/-- One chain step from a slice batch: the slice equation and the batch equation together move the
run forward by `len` steps of the base sieve. -/
public theorem segLoopSK_chain {L s lo Wm1 b b' c start len rest : Nat}
    (hP : L = segLoopK s lo Wm1 b start (len.add rest))
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSK c lo Wm1 b start len).beq b') :
    L = segLoopK s lo Wm1 b' (start.add len) rest := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSK_eq fun i hi => testBitK_slice hi] at h
  exact segLoopK_chain hP h

/-- Last chain step from a slice batch. -/
public theorem segLoopSK_last {L s lo Wm1 b b' c start len : Nat}
    (hP : L = segLoopK s lo Wm1 b start len)
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSK c lo Wm1 b start len).beq b') :
    L = b' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSK_eq fun i hi => testBitK_slice hi] at h
  exact segLoopK_last hP h

/-- A slice batch as a standalone equation about the base sieve, for the join tree. -/
public theorem segLoopSK_leaf {s lo Wm1 b b' c start len : Nat}
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSK c lo Wm1 b start len).beq b') :
    segLoopK s lo Wm1 b start len = b' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSK_eq fun i hi => testBitK_slice hi] at h
  exact Nat.beq_eq.mp h

/-- A clamped slice batch as a standalone equation, for the join tree. -/
public theorem segLoopSCK_leaf {s lo Wm1 n b b' c start len : Nat}
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSCK c lo Wm1 n b start len).beq b') :
    segLoopCK s lo Wm1 n b start len = b' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSCK_eq fun i hi => testBitK_slice hi] at h
  exact Nat.beq_eq.mp h

/-- A batch of joined masks as a standalone equation about the base sieve. -/
public theorem segAccLoopSK_leaf {s lo Wm1 n acc acc' c start len : Nat}
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segAccLoopSK c lo Wm1 n acc start len).beq acc') :
    segAccLoopK s lo Wm1 n acc start len = acc' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segAccLoopSK_eq fun i hi => testBitK_slice hi] at h
  exact Nat.beq_eq.mp h

/-- Two neighbouring stretches of joined masks join into one. -/
public theorem segAccLoopK_join {s lo Wm1 n acc acc' acc'' start len rest : Nat}
    (h1 : segAccLoopK s lo Wm1 n acc start len = acc')
    (h2 : segAccLoopK s lo Wm1 n acc' (start.add len) rest = acc'') :
    segAccLoopK s lo Wm1 n acc start (len.add rest) = acc'' := by
  rw [Nat.add_eq, segAccLoopK_add, h1]
  rwa [Nat.add_eq] at h2

/-- The window with every joined mask removed at once, as the run's value. -/
public theorem segLoopCK_of_acc {s lo Wm1 W n acc bits fuel : Nat}
    (hacc : segAccLoopK s lo Wm1 n 0 1 fuel = acc)
    (hb : (Nat.sub (initSegK W) (Nat.land acc (initSegK W))).beq bits) :
    segLoopCK s lo Wm1 n (initSegK W) 1 fuel = bits := by
  rw [segLoopCK_ldiff_total, hacc, ldiff_eq_sub]
  exact Nat.beq_eq.mp hb

/-- One chain step from a clamped slice batch. -/
public theorem segLoopSCK_chain {L s lo Wm1 n b b' c start len rest : Nat}
    (hP : L = segLoopCK s lo Wm1 n b start (len.add rest))
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSCK c lo Wm1 n b start len).beq b') :
    L = segLoopCK s lo Wm1 n b' (start.add len) rest := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSCK_eq fun i hi => testBitK_slice hi] at h
  exact segLoopCK_chain hP h

/-- Last chain step from a clamped slice batch. -/
public theorem segLoopSCK_last {L s lo Wm1 n b b' c start len : Nat}
    (hP : L = segLoopCK s lo Wm1 n b start len)
    (hc : (Nat.land (Nat.shiftRight s start) (Nat.sub (Nat.shiftLeft 1 len) 1)).beq c)
    (h : (segLoopSCK c lo Wm1 n b start len).beq b') :
    L = b' := by
  rw [Nat.beq_eq] at hc
  subst hc
  rw [segLoopSCK_eq fun i hi => testBitK_slice hi] at h
  exact segLoopCK_last hP h

/-! ## The tree fold's correctness

The kernel places each strike itself by dispatching on the bits of a leaf number, so a batch owes
one equation against the assembled mask rather than three, and the record bound `c < 2 ^ len`
disappears: the fold only reads positions below `len`, where a record could name any position and
had to be stopped from forging a tally bit. -/

/-- A mask of `n` ones is a remainder. -/
theorem land_mask_eq {k n : Nat} : k.land (2 ^ n - 1) = k % 2 ^ n := by
  have h : k.land (2 ^ n - 1) = k &&& (2 ^ n - 1) := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

/-- A shift is a division. -/
theorem shiftRightK_eq {k n : Nat} : k.shiftRight n = k / 2 ^ n := by
  have h : k.shiftRight n = k >>> n := rfl
  rw [h, Nat.shiftRight_eq_div_pow]

/-- Bit `m` splits a remainder. `lia` reads `2 ^ m * (k / 2 ^ m)` as a product of two unknowns and
cannot close this, so the three products are named first. -/
theorem land_split_lit {k a m : Nat} (ha : a = 2 ^ m) (hb : (2 : Nat) ^ (m + 1) = 2 * a) :
    k % (2 * a) = a * ((k / a) % 2) + k % a := by
  subst ha
  have h1 : 2 ^ m * (k / 2 ^ m) + k % 2 ^ m = k := Nat.div_add_mod k (2 ^ m)
  have h2 : 2 * (k / 2 ^ m / 2) + (k / 2 ^ m) % 2 = k / 2 ^ m := Nat.div_add_mod _ 2
  have h3 : 2 * 2 ^ m * (k / (2 * 2 ^ m)) + k % (2 * 2 ^ m) = k := Nat.div_add_mod k _
  have h4 : k / (2 * 2 ^ m) = k / 2 ^ m / 2 := by
    rw [Nat.mul_comm]
    exact (Nat.div_div_eq_div_mul k (2 ^ m) 2).symm
  rw [h4] at h3
  have hd : 2 ^ m * (k / 2 ^ m)
      = 2 * 2 ^ m * (k / 2 ^ m / 2) + 2 ^ m * ((k / 2 ^ m) % 2) := by
    have e : 2 * 2 ^ m * (k / 2 ^ m / 2) = 2 ^ m * (2 * (k / 2 ^ m / 2)) := by
      rw [Nat.mul_comm 2 (2 ^ m), Nat.mul_assoc]
    rw [e, ← Nat.mul_add, h2]
  generalize 2 ^ m * (k / 2 ^ m) = A at h1 hd
  generalize 2 * 2 ^ m * (k / 2 ^ m / 2) = B at h3 hd
  generalize 2 ^ m * ((k / 2 ^ m) % 2) = C at hd ⊢
  lia

/-- The same split in the `land`/`shiftRight` form the definitions use. -/
theorem land_split_at {k : Nat} (m a b : Nat) (ha : a = 2 ^ m) (hb : b = 2 * a) :
    k.land (b - 1) = a * ((k.shiftRight m).land 1) + k.land (a - 1) := by
  subst ha
  subst hb
  have hpow : 2 * 2 ^ m = 2 ^ (m + 1) := by
    rw [Nat.pow_succ]
    lia
  have e1 : (k / 2 ^ m).land 1 = (k / 2 ^ m) % 2 := by
    have h : (k / 2 ^ m).land 1 = (k / 2 ^ m).land (2 ^ 1 - 1) := rfl
    have hp : (2 : Nat) ^ 1 = 2 := rfl
    rw [h, land_mask_eq, hp]
  rw [hpow, land_mask_eq, land_mask_eq, shiftRightK_eq, e1, ← hpow]
  exact land_split_lit rfl hpow.symm

/-- One bit is zero or one. -/
theorem land1_lt {k : Nat} : k.land 1 < 2 := by
  have h : k.land 1 = k % 2 := by
    have hh : k.land 1 = k.land (2 ^ 1 - 1) := rfl
    have h2 : (2 : Nat) ^ 1 = 2 := rfl
    rw [hh, land_mask_eq, h2]
  rw [h]
  exact Nat.mod_lt _ (by lia)

/-- A guarded shift names one place. No hypothesis: `j - w = x` and `j = w + x` agree on both sides
of the guard. -/
theorem shift_key {j w x : Nat} :
    (decide (j ≥ w) && decide (j - w = x)) = decide (j = w + x) := by
  rcases Nat.lt_or_ge j w with h | h
  · have ha : ¬ (j ≥ w) := by lia
    have hbb : ¬ (j = w + x) := by lia
    rw [decide_eq_false ha, Bool.false_and, decide_eq_false hbb]
  · have hbb : (j - w = x) ↔ (j = w + x) := by
      constructor <;> intro hh <;> lia
    rw [decide_eq_true h, Bool.true_and]
    exact decide_eq_decide.mpr hbb

/-- Bit 1. -/
theorem land3_split {k : Nat} : k.land 3 = 2 * ((k.shiftRight 1).land 1) + k.land 1 :=
  land_split_at 1 2 4 rfl rfl

/-- Bit 2. -/
theorem land7_split {k : Nat} : k.land 7 = 4 * ((k.shiftRight 2).land 1) + k.land 3 :=
  land_split_at 2 4 8 rfl rfl

/-- Bit 3. -/
theorem land15_split {k : Nat} : k.land 15 = 8 * ((k.shiftRight 3).land 1) + k.land 7 :=
  land_split_at 3 8 16 rfl rfl

/-- Bit 4. -/
theorem land31_split {k : Nat} : k.land 31 = 16 * ((k.shiftRight 4).land 1) + k.land 15 :=
  land_split_at 4 16 32 rfl rfl

/-- Bit 5. -/
theorem land63_split {k : Nat} : k.land 63 = 32 * ((k.shiftRight 5).land 1) + k.land 31 :=
  land_split_at 5 32 64 rfl rfl

/-- Bit 6, the top of a 128-leaf tree. -/
theorem land127_split {k : Nat} : k.land 127 = 64 * ((k.shiftRight 6).land 1) + k.land 63 :=
  land_split_at 6 64 128 rfl rfl

/-- One level: updating a leaf pair and flattening sets exactly the bit named. Stated on
`k.land 1` rather than on `k < 2`, because `upd2` hands the whole leaf number down and each level
masks its own bit out of it. -/
theorem testBit_flat1_upd1 {t : Lvl1} {k b j : Nat} :
    (flat1 (upd1 t k b)).testBit j
      = ((flat1 t).testBit j || decide (j = (k.land 1) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  have hone : ∀ a x : Nat, ((1 : Nat) <<< a).testBit x = decide (x = a) := by
    intro a x
    have hs : (1 : Nat) <<< a = Nat.shiftLeft 1 a := rfl
    rw [hs, testBit_oneShift]
    cases h : Nat.beq x a with
    | true => simp [Nat.eq_of_beq_eq_true h]
    | false => simp [Nat.ne_of_beq_eq_false h]
  unfold upd1 flat1
  cases hbit : Nat.beq (k.land 1) 0 with
  | true =>
    have hz : k.land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, hone]
    rw [hz]
    have hzz : (0 : Nat) * 65536 + b = b := by lia
    rw [hzz]
    cases t.1.testBit j <;> cases decide (j = b) <;>
      cases (decide (j ≥ 65536) && t.2.testBit (j - 65536)) <;> rfl
  | false =>
    have h1 : k.land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k)
      lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, hone]
    rw [h1]
    have hkey : (decide (j ≥ 65536) && decide (j - 65536 = b))
        = decide (j = 1 * 65536 + b) := by
      rw [shift_key]
    rw [← hkey]
    cases t.1.testBit j <;> cases decide (j ≥ 65536) <;>
      cases t.2.testBit (j - 65536) <;> cases decide (j - 65536 = b) <;> rfl

/-- The second level, same shape with the width doubled. -/
theorem testBit_flat2_upd2 {t : Lvl2} {k b j : Nat} (_hb : b < 65536) :
    (flat2 (upd2 t k b)).testBit j
      = ((flat2 t).testBit j || decide (j = (k.land 3) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd2 flat2
  cases hbit : Nat.beq ((k.shiftRight 1).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 1).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 3 = k.land 1 := by rw [land3_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat1_upd1]
    rw [h3]
    cases (flat1 t.1).testBit j <;> cases decide (j = (k.land 1) * 65536 + b) <;>
      cases (decide (j ≥ 131072) && (flat1 t.2).testBit (j - 131072)) <;> rfl
  | false =>
    have hz : (k.shiftRight 1).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 1)
      lia
    have h3 : k.land 3 = 2 + k.land 1 := by rw [land3_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat1_upd1]
    have hkey : (decide (j ≥ 131072) && decide (j - 131072 = (k.land 1) * 65536 + b))
        = decide (j = (k.land 3) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 131072 + ((k.land 1) * 65536 + b) = (2 + k.land 1) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat1 t.1).testBit j <;> cases decide (j ≥ 131072) <;>
      cases (flat1 t.2).testBit (j - 131072) <;>
      cases decide (j - 131072 = (k.land 1) * 65536 + b) <;> rfl

/-- The third level. -/
theorem testBit_flat3_upd3 {t : Lvl3} {k b j : Nat} (hb : b < 65536) :
    (flat3 (upd3 t k b)).testBit j
      = ((flat3 t).testBit j || decide (j = (k.land 7) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd3 flat3
  cases hbit : Nat.beq ((k.shiftRight 2).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 2).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 7 = k.land 3 := by rw [land7_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat2_upd2 hb]
    rw [h3]
    cases (flat2 t.1).testBit j <;> cases decide (j = (k.land 3) * 65536 + b) <;>
      cases (decide (j ≥ 262144) && (flat2 t.2).testBit (j - 262144)) <;> rfl
  | false =>
    have hz : (k.shiftRight 2).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 2)
      lia
    have h3 : k.land 7 = 4 + k.land 3 := by rw [land7_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat2_upd2 hb]
    have hkey : (decide (j ≥ 262144) && decide (j - 262144 = (k.land 3) * 65536 + b))
        = decide (j = (k.land 7) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 262144 + ((k.land 3) * 65536 + b) = (4 + k.land 3) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat2 t.1).testBit j <;> cases decide (j ≥ 262144) <;>
      cases (flat2 t.2).testBit (j - 262144) <;>
      cases decide (j - 262144 = (k.land 3) * 65536 + b) <;> rfl

/-- The fourth level. -/
theorem testBit_flat4_upd4 {t : Lvl4} {k b j : Nat} (hb : b < 65536) :
    (flat4 (upd4 t k b)).testBit j
      = ((flat4 t).testBit j || decide (j = (k.land 15) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd4 flat4
  cases hbit : Nat.beq ((k.shiftRight 3).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 3).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 15 = k.land 7 := by rw [land15_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat3_upd3 hb]
    rw [h3]
    cases (flat3 t.1).testBit j <;> cases decide (j = (k.land 7) * 65536 + b) <;>
      cases (decide (j ≥ 524288) && (flat3 t.2).testBit (j - 524288)) <;> rfl
  | false =>
    have hz : (k.shiftRight 3).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 3)
      lia
    have h3 : k.land 15 = 8 + k.land 7 := by rw [land15_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat3_upd3 hb]
    have hkey : (decide (j ≥ 524288) && decide (j - 524288 = (k.land 7) * 65536 + b))
        = decide (j = (k.land 15) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 524288 + ((k.land 7) * 65536 + b) = (8 + k.land 7) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat3 t.1).testBit j <;> cases decide (j ≥ 524288) <;>
      cases (flat3 t.2).testBit (j - 524288) <;>
      cases decide (j - 524288 = (k.land 7) * 65536 + b) <;> rfl

/-- The fifth level. -/
theorem testBit_flat5_upd5 {t : Lvl5} {k b j : Nat} (hb : b < 65536) :
    (flat5 (upd5 t k b)).testBit j
      = ((flat5 t).testBit j || decide (j = (k.land 31) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd5 flat5
  cases hbit : Nat.beq ((k.shiftRight 4).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 4).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 31 = k.land 15 := by rw [land31_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat4_upd4 hb]
    rw [h3]
    cases (flat4 t.1).testBit j <;> cases decide (j = (k.land 15) * 65536 + b) <;>
      cases (decide (j ≥ 1048576) && (flat4 t.2).testBit (j - 1048576)) <;> rfl
  | false =>
    have hz : (k.shiftRight 4).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 4)
      lia
    have h3 : k.land 31 = 16 + k.land 15 := by rw [land31_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat4_upd4 hb]
    have hkey : (decide (j ≥ 1048576) && decide (j - 1048576 = (k.land 15) * 65536 + b))
        = decide (j = (k.land 31) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 1048576 + ((k.land 15) * 65536 + b) = (16 + k.land 15) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat4 t.1).testBit j <;> cases decide (j ≥ 1048576) <;>
      cases (flat4 t.2).testBit (j - 1048576) <;>
      cases decide (j - 1048576 = (k.land 15) * 65536 + b) <;> rfl

/-- The sixth level, which spans the whole window. -/
theorem testBit_flat6_upd6 {t : Lvl6} {k b j : Nat} (hb : b < 65536) :
    (flat6 (upd6 t k b)).testBit j
      = ((flat6 t).testBit j || decide (j = (k.land 63) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd6 flat6
  cases hbit : Nat.beq ((k.shiftRight 5).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 5).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 63 = k.land 31 := by rw [land63_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat5_upd5 hb]
    rw [h3]
    cases (flat5 t.1).testBit j <;> cases decide (j = (k.land 31) * 65536 + b) <;>
      cases (decide (j ≥ 2097152) && (flat5 t.2).testBit (j - 2097152)) <;> rfl
  | false =>
    have hz : (k.shiftRight 5).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 5)
      lia
    have h3 : k.land 63 = 32 + k.land 31 := by rw [land63_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat5_upd5 hb]
    have hkey : (decide (j ≥ 2097152) && decide (j - 2097152 = (k.land 31) * 65536 + b))
        = decide (j = (k.land 63) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 2097152 + ((k.land 31) * 65536 + b) = (32 + k.land 31) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat5 t.1).testBit j <;> cases decide (j ≥ 2097152) <;>
      cases (flat5 t.2).testBit (j - 2097152) <;>
      cases decide (j - 2097152 = (k.land 31) * 65536 + b) <;> rfl

/-- The seventh level, which the window never reaches but the definitions still carry. -/
theorem testBit_flat7_upd7 {t : Lvl7} {k b j : Nat} (hb : b < 65536) :
    (flat7 (upd7 t k b)).testBit j
      = ((flat7 t).testBit j || decide (j = (k.land 127) * 65536 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd7 flat7
  cases hbit : Nat.beq ((k.shiftRight 6).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 6).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 127 = k.land 63 := by rw [land127_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat6_upd6 hb]
    rw [h3]
    cases (flat6 t.1).testBit j <;> cases decide (j = (k.land 63) * 65536 + b) <;>
      cases (decide (j ≥ 4194304) && (flat6 t.2).testBit (j - 4194304)) <;> rfl
  | false =>
    have hz : (k.shiftRight 6).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 6)
      lia
    have h3 : k.land 127 = 64 + k.land 63 := by rw [land127_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_flat6_upd6 hb]
    have hkey : (decide (j ≥ 4194304) && decide (j - 4194304 = (k.land 63) * 65536 + b))
        = decide (j = (k.land 127) * 65536 + b) := by
      rw [h3, shift_key]
      have harith : 4194304 + ((k.land 63) * 65536 + b) = (64 + k.land 63) * 65536 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (flat6 t.1).testBit j <;> cases decide (j ≥ 4194304) <;>
      cases (flat6 t.2).testBit (j - 4194304) <;>
      cases decide (j - 4194304 = (k.land 63) * 65536 + b) <;> rfl

/-- A failed `blt` is the reverse inequality. -/
theorem blt_false_le {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  by_contra hc
  have h1 : Nat.ble (a + 1) b = true := Nat.ble_eq_true_of_le (by lia)
  have h2 : Nat.blt a b = true := h1
  rw [h2] at h
  exact Bool.noConfusion h

/-- Putting one strike into the tree sets exactly that position, and nothing when the strike falls
past the window's end. -/
theorem testBit_putK {t : Lvl7} {Wm1 s j : Nat} (hW : Wm1 < 4194304) :
    (flat7 (putK t Wm1 s)).testBit j
      = ((flat7 t).testBit j || (decide (s ≤ Wm1) && decide (j = s))) := by
  unfold putK
  cases hblt : Nat.blt Wm1 s with
  | true =>
    have hgt : Wm1 < s := Nat.le_of_ble_eq_true hblt
    have hno : ¬ (s ≤ Wm1) := by lia
    rw [decide_eq_false hno, Bool.false_and, Bool.or_false]
  | false =>
    have hle : s ≤ Wm1 := blt_false_le hblt
    have hb : s.land 65535 < 65536 := by
      have h : s.land 65535 = s % 65536 := by
        have hh : s.land 65535 = s.land (2 ^ 16 - 1) := rfl
        have h2 : (2 : Nat) ^ 16 = 65536 := rfl
        rw [hh, land_mask_eq, h2]
      rw [h]
      exact Nat.mod_lt _ (by lia)
    have hsr : s.shiftRight 16 = s / 65536 := by
      have h := shiftRightK_eq (k := s) (n := 16)
      have h2 : (2 : Nat) ^ 16 = 65536 := rfl
      rw [h2] at h
      exact h
    have hl : s.land 65535 = s % 65536 := by
      have hh : s.land 65535 = s.land (2 ^ 16 - 1) := rfl
      have h2 : (2 : Nat) ^ 16 = 65536 := rfl
      rw [hh, land_mask_eq, h2]
    have hk : (s.shiftRight 16).land 127 = s.shiftRight 16 := by
      have hlt : s / 65536 < 128 := by
        have : s < 4194304 := by lia
        lia
      have hm : (s / 65536).land 127 = (s / 65536) % 128 := by
        have hh : (s / 65536).land 127 = (s / 65536).land (2 ^ 7 - 1) := rfl
        have h2 : (2 : Nat) ^ 7 = 128 := rfl
        rw [hh, land_mask_eq, h2]
      rw [hsr, hm]
      exact Nat.mod_eq_of_lt hlt
    have hpos : (s.shiftRight 16).land 127 * 65536 + s.land 65535 = s := by
      rw [hk, hsr, hl]
      have := Nat.div_add_mod s 65536
      lia
    rw [testBit_flat7_upd7 hb, hpos, decide_eq_true hle, Bool.true_and]

/-- The two strikes of one divisor. -/
theorem testBit_treeDiv2K {t : Lvl7} {lo Wm1 p j : Nat} (hW : Wm1 < 4194304) :
    (flat7 (treeDiv2K t lo Wm1 p)).testBit j
      = ((flat7 t).testBit j
          || (decide (firstLocK (indexK (p.mul 5)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 5)) lo (p.mul 2)))
          || (decide (firstLocK (indexK (p.mul 7)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 7)) lo (p.mul 2)))) := by
  unfold treeDiv2K
  rw [testBit_putK hW, testBit_putK hW]

/-- Shifting a join is joining the shifts. -/
theorem shiftLeft_lor {a b n : Nat} : (a ||| b) <<< n = (a <<< n) ||| (b <<< n) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_or]
  cases Nat.decLe n j <;> cases a.testBit (j - n) <;> cases b.testBit (j - n) <;> rfl

/-- Joining a whole leaf at the bottom level, as an equation on the flattened pair. The other six
levels follow this shape with the width doubled, so the offset a level contributes is its own bit
of `k` times that level's width. -/
theorem flat1_updL1 {t : Lvl1} {k v : Nat} :
    flat1 (updL1 t k v) = flat1 t ||| (v <<< ((k.land 1) * 65536)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold updL1 flat1
  cases hbit : Nat.beq (k.land 1) 0 with
  | true =>
    rw [Nat.eq_of_beq_eq_true hbit]
    simp only [hlor, hsl, Nat.zero_mul, Nat.shiftLeft_zero]
    simp only [Nat.or_assoc, Nat.or_comm v (t.2 <<< 65536)]
  | false =>
    have h1 : k.land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k)
      lia
    rw [h1]
    simp only [hlor, hsl, Nat.one_mul, shiftLeft_lor]
    rw [← Nat.or_assoc]

/-- The second level, same shape with the width doubled. -/
theorem flat2_updL2 {t : Lvl2} {k v : Nat} :
    flat2 (updL2 t k v) = flat2 t ||| (v <<< ((k.land 3) * 65536)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold updL2 flat2
  cases hbit : Nat.beq ((k.shiftRight 1).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 1).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 3 = k.land 1 := by rw [land3_split, hz]; lia
    simp only [hlor, hsl, flat1_updL1, h3, Nat.or_assoc,
      Nat.or_comm (v <<< ((k.land 1) * 65536)) (flat1 t.2 <<< 131072)]
  | false =>
    have hz : (k.shiftRight 1).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 1)
      lia
    have harith : (k.land 3) * 65536 = (k.land 1) * 65536 + 131072 := by
      rw [land3_split, hz]
      lia
    simp only [hlor, hsl, flat1_updL1, shiftLeft_lor, harith, Nat.shiftLeft_add, Nat.or_assoc]

/-- The third level. -/
theorem flat3_updL3 {t : Lvl3} {k v : Nat} :
    flat3 (updL3 t k v) = flat3 t ||| (v <<< ((k.land 7) * 65536)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold updL3 flat3
  cases hbit : Nat.beq ((k.shiftRight 2).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 2).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 7 = k.land 3 := by rw [land7_split, hz]; lia
    simp only [hlor, hsl, flat2_updL2, h3, Nat.or_assoc,
      Nat.or_comm (v <<< ((k.land 3) * 65536)) (flat2 t.2 <<< 262144)]
  | false =>
    have hz : (k.shiftRight 2).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 2)
      lia
    have harith : (k.land 7) * 65536 = (k.land 3) * 65536 + 262144 := by
      rw [land7_split, hz]
      lia
    simp only [hlor, hsl, flat2_updL2, shiftLeft_lor, harith, Nat.shiftLeft_add, Nat.or_assoc]

/-- The fourth level. -/
theorem flat4_updL4 {t : Lvl4} {k v : Nat} :
    flat4 (updL4 t k v) = flat4 t ||| (v <<< ((k.land 15) * 65536)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold updL4 flat4
  cases hbit : Nat.beq ((k.shiftRight 3).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 3).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 15 = k.land 7 := by rw [land15_split, hz]; lia
    simp only [hlor, hsl, flat3_updL3, h3, Nat.or_assoc,
      Nat.or_comm (v <<< ((k.land 7) * 65536)) (flat3 t.2 <<< 524288)]
  | false =>
    have hz : (k.shiftRight 3).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 3)
      lia
    have harith : (k.land 15) * 65536 = (k.land 7) * 65536 + 524288 := by
      rw [land15_split, hz]
      lia
    simp only [hlor, hsl, flat3_updL3, shiftLeft_lor, harith, Nat.shiftLeft_add, Nat.or_assoc]

/-- The fifth level. -/
theorem flat5_updL5 {t : Lvl5} {k v : Nat} :
    flat5 (updL5 t k v) = flat5 t ||| (v <<< ((k.land 31) * 65536)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold updL5 flat5
  cases hbit : Nat.beq ((k.shiftRight 4).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 4).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 31 = k.land 15 := by rw [land31_split, hz]; lia
    simp only [hlor, hsl, flat4_updL4, h3, Nat.or_assoc,
      Nat.or_comm (v <<< ((k.land 15) * 65536)) (flat4 t.2 <<< 1048576)]
  | false =>
    have hz : (k.shiftRight 4).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 4)
      lia
    have harith : (k.land 31) * 65536 = (k.land 15) * 65536 + 1048576 := by
      rw [land31_split, hz]
      lia
    simp only [hlor, hsl, flat4_updL4, shiftLeft_lor, harith, Nat.shiftLeft_add, Nat.or_assoc]

/-- The sixth level. -/
theorem flat6_updL6 {t : Lvl6} {k v : Nat} :
    flat6 (updL6 t k v) = flat6 t ||| (v <<< ((k.land 63) * 65536)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold updL6 flat6
  cases hbit : Nat.beq ((k.shiftRight 5).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 5).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 63 = k.land 31 := by rw [land63_split, hz]; lia
    simp only [hlor, hsl, flat5_updL5, h3, Nat.or_assoc,
      Nat.or_comm (v <<< ((k.land 31) * 65536)) (flat5 t.2 <<< 2097152)]
  | false =>
    have hz : (k.shiftRight 5).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 5)
      lia
    have harith : (k.land 63) * 65536 = (k.land 31) * 65536 + 2097152 := by
      rw [land63_split, hz]
      lia
    simp only [hlor, hsl, flat5_updL5, shiftLeft_lor, harith, Nat.shiftLeft_add, Nat.or_assoc]

/-- The seventh level, the whole tree: joining a leaf sets exactly that leaf's bits. -/
theorem flat7_updL7 {t : Lvl7} {k v : Nat} :
    flat7 (updL7 t k v) = flat7 t ||| (v <<< ((k.land 127) * 65536)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold updL7 flat7
  cases hbit : Nat.beq ((k.shiftRight 6).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 6).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 127 = k.land 63 := by rw [land127_split, hz]; lia
    simp only [hlor, hsl, flat6_updL6, h3, Nat.or_assoc,
      Nat.or_comm (v <<< ((k.land 63) * 65536)) (flat6 t.2 <<< 4194304)]
  | false =>
    have hz : (k.shiftRight 6).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 6)
      lia
    have harith : (k.land 127) * 65536 = (k.land 63) * 65536 + 4194304 := by
      rw [land127_split, hz]
      lia
    simp only [hlor, hsl, flat6_updL6, shiftLeft_lor, harith, Nat.shiftLeft_add, Nat.or_assoc]

/-- A strike inside the window is its leaf's offset shifted to that leaf, so building it into a
leaf and joining the leaf sets the bit the strike names. -/
theorem shift_leaf_eq {s : Nat} (hs : s < 4194304) :
    (1 <<< (s.land 65535)) <<< (((s.shiftRight 16).land 127) * 65536) = 1 <<< s := by
  have hl : s.land 65535 = s % 65536 := by
    have hh : s.land 65535 = s.land (2 ^ 16 - 1) := rfl
    have h2 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [hh, land_mask_eq, h2]
  have hsr : s.shiftRight 16 = s / 65536 := by
    have h := shiftRightK_eq (k := s) (n := 16)
    have h2 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [h2] at h
    exact h
  have hk : (s.shiftRight 16).land 127 = s.shiftRight 16 := by
    have hlt : s / 65536 < 128 := by lia
    have hm : (s / 65536).land 127 = (s / 65536) % 128 := by
      have hh : (s / 65536).land 127 = (s / 65536).land (2 ^ 7 - 1) := rfl
      have h2 : (2 : Nat) ^ 7 = 128 := rfl
      rw [hh, land_mask_eq, h2]
    rw [hsr, hm]
    exact Nat.mod_eq_of_lt hlt
  have hpos : s.land 65535 + ((s.shiftRight 16).land 127) * 65536 = s := by
    rw [hk, hsr, hl]
    have := Nat.div_add_mod s 65536
    lia
  rw [← Nat.shiftLeft_add, hpos]

/-- A strike past the window's end leaves the tree alone. -/
theorem putK_eq_self {t : Lvl7} {Wm1 s : Nat} (h : Nat.blt Wm1 s = true) : putK t Wm1 s = t := by
  unfold putK
  rw [h]

/-- A divisor whose two strikes both pass the window's end leaves the tree alone. Of the 508968
divisors of the widest band, the ones in this position carry no information for the batch. -/
theorem treeDiv2K_eq_self {t : Lvl7} {lo Wm1 p : Nat}
    (hA : Nat.blt Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) = true)
    (hB : Nat.blt Wm1 (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) = true) :
    treeDiv2K t lo Wm1 p = t := by
  unfold treeDiv2K
  rw [putK_eq_self hB, putK_eq_self hA]

/-- Loop recurrence for the widest band's fold, in the `Bool.rec` form the definition uses. -/
theorem treeFold2K_succ {c lo Wm1 start len : Nat} :
    treeFold2K c lo Wm1 start (len + 1)
      = (testBitK c len).rec (treeFold2K c lo Wm1 start len)
          (treeDiv2K (treeFold2K c lo Wm1 start len) lo Wm1 (valueK (start.add len))) := rfl

/-- Two batches assemble the same tree when they name the same divisors at every position whose
divisor strikes inside the window, so a batch may leave out the divisors that strike nowhere.

The hypothesis at a left-out position names the same two `firstLocK` values that `treeDiv2K`
applies there, so a batch filtered this way still carries them. -/
theorem treeFold2K_congr {c d lo Wm1 start : Nat} : ∀ {len : Nat},
    (∀ i, i < len → testBitK c i = testBitK d i
      ∨ (Nat.blt Wm1 (firstLocK (indexK ((valueK (start.add i)).mul 5)) lo
            ((valueK (start.add i)).mul 2)) = true
        ∧ Nat.blt Wm1 (firstLocK (indexK ((valueK (start.add i)).mul 7)) lo
            ((valueK (start.add i)).mul 2)) = true)) →
    treeFold2K c lo Wm1 start len = treeFold2K d lo Wm1 start len
  | 0, _ => rfl
  | n + 1, h => by
    rw [treeFold2K_succ, treeFold2K_succ,
      treeFold2K_congr (fun i hi => h i (Nat.lt_succ_of_lt hi))]
    rcases h n (Nat.lt_succ_self n) with heq | ⟨hA, hB⟩
    · rw [heq]
    · rw [treeDiv2K_eq_self hA hB]
      cases testBitK c n <;> cases testBitK d n <;> rfl

/-- Joining nothing to nothing gives nothing, at any width. -/
theorem lor_shift_zero {w : Nat} : (0 : Nat).lor ((0 : Nat).shiftLeft w) = 0 := by
  have h0 : (0 : Nat).shiftLeft w = 0 <<< w := rfl
  have hl : ∀ n : Nat, (0 : Nat).lor n = n := by
    intro n
    have h : (0 : Nat).lor n = 0 ||| n := rfl
    rw [h, Nat.zero_or]
  rw [hl, h0, Nat.zero_shiftLeft]

/-- An empty tree holds nothing, one level at a time. -/
theorem flat1_zero : flat1 zero1 = 0 := by
  unfold flat1 zero1
  exact lor_shift_zero

/-- Four slices. -/
theorem flat2_zero : flat2 zero2 = 0 := by
  unfold flat2 zero2
  rw [flat1_zero]
  exact lor_shift_zero

/-- Eight. -/
theorem flat3_zero : flat3 zero3 = 0 := by
  unfold flat3 zero3
  rw [flat2_zero]
  exact lor_shift_zero

/-- Sixteen. -/
theorem flat4_zero : flat4 zero4 = 0 := by
  unfold flat4 zero4
  rw [flat3_zero]
  exact lor_shift_zero

/-- Thirty-two. -/
theorem flat5_zero : flat5 zero5 = 0 := by
  unfold flat5 zero5
  rw [flat4_zero]
  exact lor_shift_zero

/-- Sixty-four. -/
theorem flat6_zero : flat6 zero6 = 0 := by
  unfold flat6 zero6
  rw [flat5_zero]
  exact lor_shift_zero

/-- The whole empty tree. -/
theorem flat7_zero : flat7 zero7 = 0 := by
  unfold flat7 zero7
  rw [flat6_zero]
  exact lor_shift_zero

/-- Building each leaf whole and joining it once gives the same mask as joining every strike into
the tree one at a time, given that each strike lies inside the window. This is what lets a batch
pay the descent once a leaf rather than once a strike. -/
theorem joinBatchK_eq {q : Nat} : ∀ {cnt : Nat},
    (∀ i, i < cnt → ((q.shiftRight (i.mul 32)).land 4294967295) < 4194304) →
    joinBatchK q cnt = orStrikesK q cnt
  | 0, _ => by
    simp only [joinBatchK, joinFoldK, orStrikesK, flat7_updL7, flat7_zero, Nat.zero_shiftLeft,
      Nat.or_self]
  | n + 1, h => by
    have hs : ((q.shiftRight (n.mul 32)).land 4294967295) < 4194304 := h n (Nat.lt_succ_self n)
    have ih := joinBatchK_eq (q := q) (cnt := n) fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hbit := shift_leaf_eq hs
    have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
    have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
    simp only [joinBatchK] at ih ⊢
    simp only [joinFoldK, orStrikesK]
    cases hb : Nat.beq (((q.shiftRight (n.mul 32)).land 4294967295).shiftRight 16)
        (joinFoldK q n).2.2 with
    | true =>
      rw [Nat.eq_of_beq_eq_true hb] at hbit
      simp only [hlor, hsl, ← ih, flat7_updL7, shiftLeft_lor, hbit, Nat.or_assoc]
    | false =>
      simp only [hlor, hsl, ← ih, flat7_updL7, hbit]

/-- What the tree holds after walking a batch: exactly the in-window strikes of the divisors the
slice names, two to a divisor. The same characterisation `testBit_segAccLoopSK_wide` gives for the
marking side, so the two meet. -/
theorem testBit_treeFold2K {c lo Wm1 start len j : Nat} (hW : Wm1 < 4194304) (hj : j ≤ Wm1) :
    (flat7 (treeFold2K c lo Wm1 start len)).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 2 ∧ testBitK c i = true
        ∧ entrySeedK lo start (8 * i + w) = j := by
  induction len with
  | zero =>
    have hz : treeFold2K c lo Wm1 start 0 = zero7 := rfl
    rw [hz, flat7_zero]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have hadd : start.add len = start + len := rfl
    have hstep : treeFold2K c lo Wm1 start (len + 1)
        = (testBitK c len).rec (treeFold2K c lo Wm1 start len)
            (treeDiv2K (treeFold2K c lo Wm1 start len) lo Wm1 (valueK (start.add len))) := rfl
    rw [hstep]
    cases hb : testBitK c len with
    | false =>
      rw [ih]
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      rw [hadd, testBit_treeDiv2K hW]
      have hA : entrySeedK lo start (8 * len + 0)
          = firstLocK (indexK ((valueK (start + len)).mul 5)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_five
      have hB : entrySeedK lo start (8 * len + 1)
          = firstLocK (indexK ((valueK (start + len)).mul 7)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_seven
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ((h | ⟨-, hjA⟩) | ⟨-, hjB⟩)
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := h
          exact ⟨i, by lia, w, hw, hc, hs⟩
        · exact ⟨len, by lia, 0, by lia, hb, by rw [hA]; exact hjA.symm⟩
        · exact ⟨len, by lia, 1, by lia, hb, by rw [hB]; exact hjB.symm⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact Or.inl (Or.inl ⟨i, h, w, hw, hc, hs⟩)
        · have hil : i = len := by lia
          rw [hil] at hs
          rcases (by lia : w = 0 ∨ w = 1) with hw0 | hw1
          · rw [hw0, hA] at hs
            exact Or.inl (Or.inr ⟨by lia, hs.symm⟩)
          · rw [hw1, hB] at hs
            exact Or.inr ⟨by lia, hs.symm⟩

/-- The tree fold removes from the window exactly what the batch's run removes. No `c < 2 ^ len`
hypothesis: the fold only ever reads positions below `len`, so a bit above it cannot reach the
answer — where the record design needed that bound to stop an entry forging a tally bit. -/
theorem segLoopSCK_eq_tree2 {c lo start len n Wm1 seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 4194304)
    (hwide : ∀ i, i < len → Wm1 < valueK (start + i) * 2) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (treeBatch2K c lo Wm1 start len) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (treeBatch2K c lo Wm1 start len).testBit j = true := by
      rw [testBit_segAccLoopSK_wide hj hwide]
      unfold treeBatch2K
      rw [testBit_treeFold2K hW hj]
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (treeBatch2K c lo Wm1 start len).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

/-- One batch of the widest band, settled by having the kernel place the strikes itself. Five
Boolean hypotheses where `stripeStep` needs eight, because there are no records to bound, no slice
lists to carry and no tally to check. -/
public theorem treeStep2 {c lo Wm1 n W start len seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hW4 : Nat.blt Wm1 4194304 = true)
    (hwide : Nat.blt Wm1 (Nat.mul (valueK start) 2) = true)
    (hbatch : Nat.beq (treeBatch2K c lo Wm1 start len) lit = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hW' : Wm1 < 4194304 := Nat.le_of_ble_eq_true hW4
  have hb := Nat.eq_of_beq_eq_true hbatch
  refine Nat.beq_eq.mpr ?_
  rw [segLoopSCK_eq_tree2 hseg hW' (wide_of_blt hwide), hb, ldiff_eq_sub]
  exact Nat.eq_of_beq_eq_true hclear

/-! ## The wide-leaf tree's correctness

The same argument as for `flat7`, at leaves of 262144 bits. Four levels span the window where
seven did, and `upd1` to `upd4` are shared, so only the flatten steps and the split of a strike
into leaf and offset are restated. -/

/-- One level, with leaves of 262144 bits. -/
theorem testBit_wflat1_upd1 {t : Lvl1} {k b j : Nat} :
    (wflat1 (upd1 t k b)).testBit j
      = ((wflat1 t).testBit j || decide (j = (k.land 1) * 262144 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  have hone : ∀ a x : Nat, ((1 : Nat) <<< a).testBit x = decide (x = a) := by
    intro a x
    have hs : (1 : Nat) <<< a = Nat.shiftLeft 1 a := rfl
    rw [hs, testBit_oneShift]
    cases h : Nat.beq x a with
    | true => simp [Nat.eq_of_beq_eq_true h]
    | false => simp [Nat.ne_of_beq_eq_false h]
  unfold upd1 wflat1
  cases hbit : Nat.beq (k.land 1) 0 with
  | true =>
    have hz : k.land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, hone]
    rw [hz]
    have hzz : (0 : Nat) * 262144 + b = b := by lia
    rw [hzz]
    cases t.1.testBit j <;> cases decide (j = b) <;>
      cases (decide (j ≥ 262144) && t.2.testBit (j - 262144)) <;> rfl
  | false =>
    have h1 : k.land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k)
      lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, hone]
    rw [h1]
    have hkey : (decide (j ≥ 262144) && decide (j - 262144 = b))
        = decide (j = 1 * 262144 + b) := by
      rw [shift_key]
    rw [← hkey]
    cases t.1.testBit j <;> cases decide (j ≥ 262144) <;>
      cases t.2.testBit (j - 262144) <;> cases decide (j - 262144 = b) <;> rfl

/-- The second level, with leaves of 262144 bits. -/
theorem testBit_wflat2_upd2 {t : Lvl2} {k b j : Nat} (_hb : b < 262144) :
    (wflat2 (upd2 t k b)).testBit j
      = ((wflat2 t).testBit j || decide (j = (k.land 3) * 262144 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd2 wflat2
  cases hbit : Nat.beq ((k.shiftRight 1).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 1).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 3 = k.land 1 := by rw [land3_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_wflat1_upd1]
    rw [h3]
    cases (wflat1 t.1).testBit j <;> cases decide (j = (k.land 1) * 262144 + b) <;>
      cases (decide (j ≥ 524288) && (wflat1 t.2).testBit (j - 524288)) <;> rfl
  | false =>
    have hz : (k.shiftRight 1).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 1)
      lia
    have h3 : k.land 3 = 2 + k.land 1 := by rw [land3_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_wflat1_upd1]
    have hkey : (decide (j ≥ 524288) && decide (j - 524288 = (k.land 1) * 262144 + b))
        = decide (j = (k.land 3) * 262144 + b) := by
      rw [h3, shift_key]
      have harith : 524288 + ((k.land 1) * 262144 + b) = (2 + k.land 1) * 262144 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (wflat1 t.1).testBit j <;> cases decide (j ≥ 524288) <;>
      cases (wflat1 t.2).testBit (j - 524288) <;>
      cases decide (j - 524288 = (k.land 1) * 262144 + b) <;> rfl

/-- The third level, with leaves of 262144 bits. -/
theorem testBit_wflat3_upd3 {t : Lvl3} {k b j : Nat} (hb : b < 262144) :
    (wflat3 (upd3 t k b)).testBit j
      = ((wflat3 t).testBit j || decide (j = (k.land 7) * 262144 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd3 wflat3
  cases hbit : Nat.beq ((k.shiftRight 2).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 2).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 7 = k.land 3 := by rw [land7_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_wflat2_upd2 hb]
    rw [h3]
    cases (wflat2 t.1).testBit j <;> cases decide (j = (k.land 3) * 262144 + b) <;>
      cases (decide (j ≥ 1048576) && (wflat2 t.2).testBit (j - 1048576)) <;> rfl
  | false =>
    have hz : (k.shiftRight 2).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 2)
      lia
    have h3 : k.land 7 = 4 + k.land 3 := by rw [land7_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_wflat2_upd2 hb]
    have hkey : (decide (j ≥ 1048576) && decide (j - 1048576 = (k.land 3) * 262144 + b))
        = decide (j = (k.land 7) * 262144 + b) := by
      rw [h3, shift_key]
      have harith : 1048576 + ((k.land 3) * 262144 + b) = (4 + k.land 3) * 262144 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (wflat2 t.1).testBit j <;> cases decide (j ≥ 1048576) <;>
      cases (wflat2 t.2).testBit (j - 1048576) <;>
      cases decide (j - 1048576 = (k.land 3) * 262144 + b) <;> rfl

/-- The fourth level, which spans the window at leaves of 262144 bits. -/
theorem testBit_wflat4_upd4 {t : Lvl4} {k b j : Nat} (hb : b < 262144) :
    (wflat4 (upd4 t k b)).testBit j
      = ((wflat4 t).testBit j || decide (j = (k.land 15) * 262144 + b)) := by
  have hlor : ∀ x y : Nat, x.lor y = x ||| y := fun _ _ => rfl
  have hsl : ∀ x y : Nat, x.shiftLeft y = x <<< y := fun _ _ => rfl
  unfold upd4 wflat4
  cases hbit : Nat.beq ((k.shiftRight 3).land 1) 0 with
  | true =>
    have hz : (k.shiftRight 3).land 1 = 0 := Nat.eq_of_beq_eq_true hbit
    have h3 : k.land 15 = k.land 7 := by rw [land15_split, hz]; lia
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_wflat3_upd3 hb]
    rw [h3]
    cases (wflat3 t.1).testBit j <;> cases decide (j = (k.land 7) * 262144 + b) <;>
      cases (decide (j ≥ 2097152) && (wflat3 t.2).testBit (j - 2097152)) <;> rfl
  | false =>
    have hz : (k.shiftRight 3).land 1 = 1 := by
      have hne := Nat.ne_of_beq_eq_false hbit
      have := land1_lt (k := k.shiftRight 3)
      lia
    have h3 : k.land 15 = 8 + k.land 7 := by rw [land15_split, hz]
    simp only [hlor, hsl, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_wflat3_upd3 hb]
    have hkey : (decide (j ≥ 2097152) && decide (j - 2097152 = (k.land 7) * 262144 + b))
        = decide (j = (k.land 15) * 262144 + b) := by
      rw [h3, shift_key]
      have harith : 2097152 + ((k.land 7) * 262144 + b) = (8 + k.land 7) * 262144 + b := by lia
      rw [harith]
    rw [← hkey]
    cases (wflat3 t.1).testBit j <;> cases decide (j ≥ 2097152) <;>
      cases (wflat3 t.2).testBit (j - 2097152) <;>
      cases decide (j - 2097152 = (k.land 7) * 262144 + b) <;> rfl

/-- Putting one strike into the wide-leaf tree sets exactly that position, and nothing when the
strike falls past the window's end. -/
theorem testBit_wputK {t : Lvl4} {Wm1 s j : Nat} (hW : Wm1 < 4194304) :
    (wflat4 (wputK t Wm1 s)).testBit j
      = ((wflat4 t).testBit j || (decide (s ≤ Wm1) && decide (j = s))) := by
  unfold wputK
  cases hblt : Nat.blt Wm1 s with
  | true =>
    have hgt : Wm1 < s := Nat.le_of_ble_eq_true hblt
    have hno : ¬ (s ≤ Wm1) := by lia
    rw [decide_eq_false hno, Bool.false_and, Bool.or_false]
  | false =>
    have hle : s ≤ Wm1 := blt_false_le hblt
    have hl : s.land 262143 = s % 262144 := by
      have hh : s.land 262143 = s.land (2 ^ 18 - 1) := rfl
      have h2 : (2 : Nat) ^ 18 = 262144 := rfl
      rw [hh, land_mask_eq, h2]
    have hb : s.land 262143 < 262144 := by
      rw [hl]
      exact Nat.mod_lt _ (by lia)
    have hsr : s.shiftRight 18 = s / 262144 := by
      have h := shiftRightK_eq (k := s) (n := 18)
      have h2 : (2 : Nat) ^ 18 = 262144 := rfl
      rw [h2] at h
      exact h
    have hk : (s.shiftRight 18).land 15 = s.shiftRight 18 := by
      have hlt : s / 262144 < 16 := by
        have : s < 4194304 := by lia
        lia
      have hm : (s / 262144).land 15 = (s / 262144) % 16 := by
        have hh : (s / 262144).land 15 = (s / 262144).land (2 ^ 4 - 1) := rfl
        have h2 : (2 : Nat) ^ 4 = 16 := rfl
        rw [hh, land_mask_eq, h2]
      rw [hsr, hm]
      exact Nat.mod_eq_of_lt hlt
    have hpos : (s.shiftRight 18).land 15 * 262144 + s.land 262143 = s := by
      rw [hk, hsr, hl]
      have := Nat.div_add_mod s 262144
      lia
    rw [testBit_wflat4_upd4 hb, hpos, decide_eq_true hle, Bool.true_and]

/-- The two strikes of one divisor, in the wide-leaf tree. -/
theorem testBit_wtreeDiv2K {t : Lvl4} {lo Wm1 p j : Nat} (hW : Wm1 < 4194304) :
    (wflat4 (wtreeDiv2K t lo Wm1 p)).testBit j
      = ((wflat4 t).testBit j
          || (decide (firstLocK (indexK (p.mul 5)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 5)) lo (p.mul 2)))
          || (decide (firstLocK (indexK (p.mul 7)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 7)) lo (p.mul 2)))) := by
  unfold wtreeDiv2K
  rw [testBit_wputK hW, testBit_wputK hW]

/-- An empty wide-leaf tree holds nothing, two leaves. -/
theorem wflat1_zero : wflat1 zero1 = 0 := by
  unfold wflat1 zero1
  exact lor_shift_zero

/-- Four. -/
theorem wflat2_zero : wflat2 zero2 = 0 := by
  unfold wflat2 zero2
  rw [wflat1_zero]
  exact lor_shift_zero

/-- Eight. -/
theorem wflat3_zero : wflat3 zero3 = 0 := by
  unfold wflat3 zero3
  rw [wflat2_zero]
  exact lor_shift_zero

/-- Sixteen, the whole empty tree. -/
theorem wflat4_zero : wflat4 zero4 = 0 := by
  unfold wflat4 zero4
  rw [wflat3_zero]
  exact lor_shift_zero

/-- What the wide-leaf tree holds after walking a batch: exactly the in-window strikes of the
divisors the slice names, two to a divisor. -/
theorem testBit_wtreeFold2K {c lo Wm1 start len j : Nat} (hW : Wm1 < 4194304) (hj : j ≤ Wm1) :
    (wflat4 (wtreeFold2K c lo Wm1 start len)).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 2 ∧ testBitK c i = true
        ∧ entrySeedK lo start (8 * i + w) = j := by
  induction len with
  | zero =>
    have hz : wtreeFold2K c lo Wm1 start 0 = zero4 := rfl
    rw [hz, wflat4_zero]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have hadd : start.add len = start + len := rfl
    have hstep : wtreeFold2K c lo Wm1 start (len + 1)
        = (testBitK c len).rec (wtreeFold2K c lo Wm1 start len)
            (wtreeDiv2K (wtreeFold2K c lo Wm1 start len) lo Wm1 (valueK (start.add len))) := rfl
    rw [hstep]
    cases hb : testBitK c len with
    | false =>
      rw [ih]
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      rw [hadd, testBit_wtreeDiv2K hW]
      have hA : entrySeedK lo start (8 * len + 0)
          = firstLocK (indexK ((valueK (start + len)).mul 5)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_five
      have hB : entrySeedK lo start (8 * len + 1)
          = firstLocK (indexK ((valueK (start + len)).mul 7)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_seven
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ((h | ⟨-, hjA⟩) | ⟨-, hjB⟩)
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := h
          exact ⟨i, by lia, w, hw, hc, hs⟩
        · exact ⟨len, by lia, 0, by lia, hb, by rw [hA]; exact hjA.symm⟩
        · exact ⟨len, by lia, 1, by lia, hb, by rw [hB]; exact hjB.symm⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact Or.inl (Or.inl ⟨i, h, w, hw, hc, hs⟩)
        · have hil : i = len := by lia
          rw [hil] at hs
          rcases (by lia : w = 0 ∨ w = 1) with hw0 | hw1
          · rw [hw0, hA] at hs
            exact Or.inl (Or.inr ⟨by lia, hs.symm⟩)
          · rw [hw1, hB] at hs
            exact Or.inr ⟨by lia, hs.symm⟩

/-- The wide-leaf tree fold removes from the window exactly what the batch's run removes. -/
theorem segLoopSCK_eq_wtree2 {c lo start len n Wm1 seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 4194304)
    (hwide : ∀ i, i < len → Wm1 < valueK (start + i) * 2) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (wtreeBatch2K c lo Wm1 start len) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (wtreeBatch2K c lo Wm1 start len).testBit j = true := by
      rw [testBit_segAccLoopSK_wide hj hwide]
      unfold wtreeBatch2K
      rw [testBit_wtreeFold2K hW hj]
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (wtreeBatch2K c lo Wm1 start len).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

/-- One batch of the widest band, settled by a tree with leaves of 262144 bits. -/
public theorem wtreeStep2 {c lo Wm1 n W start len seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hW4 : Nat.blt Wm1 4194304 = true)
    (hwide : Nat.blt Wm1 (Nat.mul (valueK start) 2) = true)
    (hbatch : Nat.beq (wtreeBatch2K c lo Wm1 start len) lit = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hW' : Wm1 < 4194304 := Nat.le_of_ble_eq_true hW4
  have hb := Nat.eq_of_beq_eq_true hbatch
  refine Nat.beq_eq.mpr ?_
  rw [segLoopSCK_eq_wtree2 hseg hW' (wide_of_blt hwide), hb, ldiff_eq_sub]
  exact Nat.eq_of_beq_eq_true hclear

/-- The four strikes of one divisor, in the wide-leaf tree. -/
theorem testBit_wtreeDiv4K {t : Lvl4} {lo Wm1 p j : Nat} (hW : Wm1 < 4194304) :
    (wflat4 (wtreeDiv4K t lo Wm1 p)).testBit j
      = ((wflat4 t).testBit j
          || (decide (firstLocK (indexK (p.mul 5)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 5)) lo (p.mul 2)))
          || (decide (firstLocK (indexK (p.mul 7)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 7)) lo (p.mul 2)))
          || (decide ((firstLocK (indexK (p.mul 5)) lo (p.mul 2)).add (p.mul 2) ≤ Wm1)
              && decide (j = (firstLocK (indexK (p.mul 5)) lo (p.mul 2)).add (p.mul 2)))
          || (decide ((firstLocK (indexK (p.mul 7)) lo (p.mul 2)).add (p.mul 2) ≤ Wm1)
              && decide (j = (firstLocK (indexK (p.mul 7)) lo (p.mul 2)).add (p.mul 2)))) := by
  unfold wtreeDiv4K
  rw [testBit_wputK hW, testBit_wputK hW, testBit_wputK hW, testBit_wputK hW]

/-- What the wide-leaf tree holds after walking a batch of the four-strike band. -/
theorem testBit_wtreeFold4K {c lo Wm1 start len j : Nat} (hW : Wm1 < 4194304) (hj : j ≤ Wm1) :
    (wflat4 (wtreeFold4K c lo Wm1 start len)).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 4 ∧ testBitK c i = true
        ∧ entrySeedK lo start (8 * i + w) = j := by
  induction len with
  | zero =>
    have hz : wtreeFold4K c lo Wm1 start 0 = zero4 := rfl
    rw [hz, wflat4_zero]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have hadd : start.add len = start + len := rfl
    have hstep : wtreeFold4K c lo Wm1 start (len + 1)
        = (testBitK c len).rec (wtreeFold4K c lo Wm1 start len)
            (wtreeDiv4K (wtreeFold4K c lo Wm1 start len) lo Wm1 (valueK (start.add len))) := rfl
    rw [hstep]
    cases hb : testBitK c len with
    | false =>
      rw [ih]
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      rw [hadd, testBit_wtreeDiv4K hW]
      have h0 : entrySeedK lo start (8 * len + 0)
          = firstLocK (indexK ((valueK (start + len)).mul 5)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_five
      have h1 : entrySeedK lo start (8 * len + 1)
          = firstLocK (indexK ((valueK (start + len)).mul 7)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_seven
      have h2 : entrySeedK lo start (8 * len + 2)
          = (firstLocK (indexK ((valueK (start + len)).mul 5)) lo
              ((valueK (start + len)).mul 2)).add ((valueK (start + len)).mul 2) :=
        entrySeedK_five'
      have h3 : entrySeedK lo start (8 * len + 3)
          = (firstLocK (indexK ((valueK (start + len)).mul 7)) lo
              ((valueK (start + len)).mul 2)).add ((valueK (start + len)).mul 2) :=
        entrySeedK_seven'
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ((((h | ⟨-, e⟩) | ⟨-, e⟩) | ⟨-, e⟩) | ⟨-, e⟩)
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := h
          exact ⟨i, by lia, w, hw, hc, hs⟩
        · exact ⟨len, by lia, 0, by lia, hb, by rw [h0]; exact e.symm⟩
        · exact ⟨len, by lia, 1, by lia, hb, by rw [h1]; exact e.symm⟩
        · exact ⟨len, by lia, 2, by lia, hb, by rw [h2]; exact e.symm⟩
        · exact ⟨len, by lia, 3, by lia, hb, by rw [h3]; exact e.symm⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨i, h, w, hw, hc, hs⟩)))
        · have hil : i = len := by lia
          rw [hil] at hs
          rcases (by lia : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3) with hw0 | hw1 | hw2 | hw3
          · rw [hw0, h0] at hs
            exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by lia, hs.symm⟩)))
          · rw [hw1, h1] at hs
            exact Or.inl (Or.inl (Or.inr ⟨by lia, hs.symm⟩))
          · rw [hw2, h2] at hs
            exact Or.inl (Or.inr ⟨by lia, hs.symm⟩)
          · rw [hw3, h3] at hs
            exact Or.inr ⟨by lia, hs.symm⟩

/-- The wide-leaf tree removes from the window exactly what a four-strike batch's run removes. -/
theorem segLoopSCK_eq_wtree4 {c lo start len n Wm1 seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 4194304) (hn : 1 ≤ n)
    (hband : ∀ i, i < len → valueK (start + i) * 2 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 4) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (wtreeBatch4K c lo Wm1 start len) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (wtreeBatch4K c lo Wm1 start len).testBit j = true := by
      rw [testBit_segAccLoopSK_band hj hn hband]
      unfold wtreeBatch4K
      rw [testBit_wtreeFold4K hW hj]
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (wtreeBatch4K c lo Wm1 start len).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

/-- One batch of the four-strike band, settled by a tree with leaves of 262144 bits. -/
public theorem wtreeStep4 {c lo Wm1 n W start len seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hW4 : Nat.blt Wm1 4194304 = true) (hn : Nat.ble 1 n = true)
    (hlast : Nat.ble (Nat.mul (valueK (start + len)) 2) Wm1 = true)
    (hfirst : Nat.blt Wm1 (Nat.mul (valueK start) 4) = true)
    (hbatch : Nat.beq (wtreeBatch4K c lo Wm1 start len) lit = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hW' : Wm1 < 4194304 := Nat.le_of_ble_eq_true hW4
  have hb := Nat.eq_of_beq_eq_true hbatch
  refine Nat.beq_eq.mpr ?_
  rw [segLoopSCK_eq_wtree4 hseg hW' (Nat.le_of_ble_eq_true hn) (band_of_tests hlast hfirst), hb,
    ldiff_eq_sub]
  exact Nat.eq_of_beq_eq_true hclear

/-- The eight strikes of one divisor, in the wide-leaf tree. -/
theorem testBit_wtreeDivK {t : Lvl4} {lo Wm1 p j : Nat} (hW : Wm1 < 4194304) :
    (wflat4 (wtreeDivK t lo Wm1 p)).testBit j
      = ((wflat4 t).testBit j
          || (decide (firstLocK (indexK (p.mul 5)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 5)) lo (p.mul 2)))
          || (decide (firstLocK (indexK (p.mul 7)) lo (p.mul 2) ≤ Wm1)
              && decide (j = firstLocK (indexK (p.mul 7)) lo (p.mul 2)))
          || (decide ((firstLocK (indexK (p.mul 5)) lo (p.mul 2)).add (p.mul 2) ≤ Wm1)
              && decide (j = (firstLocK (indexK (p.mul 5)) lo (p.mul 2)).add (p.mul 2)))
          || (decide ((firstLocK (indexK (p.mul 7)) lo (p.mul 2)).add (p.mul 2) ≤ Wm1)
              && decide (j = (firstLocK (indexK (p.mul 7)) lo (p.mul 2)).add (p.mul 2)))
          || (decide ((firstLocK (indexK (p.mul 5)) lo (p.mul 2)).add (p.mul 4) ≤ Wm1)
              && decide (j = (firstLocK (indexK (p.mul 5)) lo (p.mul 2)).add (p.mul 4)))
          || (decide ((firstLocK (indexK (p.mul 7)) lo (p.mul 2)).add (p.mul 4) ≤ Wm1)
              && decide (j = (firstLocK (indexK (p.mul 7)) lo (p.mul 2)).add (p.mul 4)))
          || (decide ((firstLocK (indexK (p.mul 5)) lo (p.mul 2)).add (p.mul 2 + p.mul 4) ≤ Wm1)
              && decide (j = (firstLocK (indexK (p.mul 5)) lo (p.mul 2)).add (p.mul 2 + p.mul 4)))
          || (decide ((firstLocK (indexK (p.mul 7)) lo (p.mul 2)).add (p.mul 2 + p.mul 4) ≤ Wm1)
              && decide (j = (firstLocK (indexK (p.mul 7)) lo (p.mul 2)).add
                (p.mul 2 + p.mul 4)))) := by
  unfold wtreeDivK
  rw [testBit_wputK hW, testBit_wputK hW, testBit_wputK hW, testBit_wputK hW,
    testBit_wputK hW, testBit_wputK hW, testBit_wputK hW, testBit_wputK hW]

/-- What the wide-leaf tree holds after walking a batch of the eight-strike band. -/
theorem testBit_wtreeFoldK {c lo Wm1 start len j : Nat} (hW : Wm1 < 4194304) (hj : j ≤ Wm1) :
    (wflat4 (wtreeFoldK c lo Wm1 start len)).testBit j = true ↔
      ∃ i, i < len ∧ ∃ w, w < 8 ∧ testBitK c i = true
        ∧ entrySeedK lo start (8 * i + w) = j := by
  induction len with
  | zero =>
    have hz : wtreeFoldK c lo Wm1 start 0 = zero4 := rfl
    rw [hz, wflat4_zero]
    constructor
    · intro h
      simp at h
    · rintro ⟨i, hi, -⟩
      lia
  | succ len ih =>
    have hadd : start.add len = start + len := rfl
    have hstep : wtreeFoldK c lo Wm1 start (len + 1)
        = (testBitK c len).rec (wtreeFoldK c lo Wm1 start len)
            (wtreeDivK (wtreeFoldK c lo Wm1 start len) lo Wm1 (valueK (start.add len))) := rfl
    rw [hstep]
    cases hb : testBitK c len with
    | false =>
      rw [ih]
      constructor
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        exact ⟨i, by lia, w, hw, hc, hs⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact ⟨i, h, w, hw, hc, hs⟩
        · have hil : i = len := by lia
          rw [hil, hb] at hc
          simp at hc
    | true =>
      rw [hadd, testBit_wtreeDivK hW]
      have h0 : entrySeedK lo start (8 * len + 0)
          = firstLocK (indexK ((valueK (start + len)).mul 5)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_five
      have h1 : entrySeedK lo start (8 * len + 1)
          = firstLocK (indexK ((valueK (start + len)).mul 7)) lo ((valueK (start + len)).mul 2) :=
        entrySeedK_seven
      have h2 : entrySeedK lo start (8 * len + 2)
          = (firstLocK (indexK ((valueK (start + len)).mul 5)) lo
              ((valueK (start + len)).mul 2)).add ((valueK (start + len)).mul 2) :=
        entrySeedK_five'
      have h3 : entrySeedK lo start (8 * len + 3)
          = (firstLocK (indexK ((valueK (start + len)).mul 7)) lo
              ((valueK (start + len)).mul 2)).add ((valueK (start + len)).mul 2) :=
        entrySeedK_seven'
      have h4 : entrySeedK lo start (8 * len + 4)
          = (firstLocK (indexK ((valueK (start + len)).mul 5)) lo
              ((valueK (start + len)).mul 2)).add ((valueK (start + len)).mul 4) :=
        entrySeedK_five4
      have h5 : entrySeedK lo start (8 * len + 5)
          = (firstLocK (indexK ((valueK (start + len)).mul 7)) lo
              ((valueK (start + len)).mul 2)).add ((valueK (start + len)).mul 4) :=
        entrySeedK_seven4
      have h6 : entrySeedK lo start (8 * len + 6)
          = (firstLocK (indexK ((valueK (start + len)).mul 5)) lo
              ((valueK (start + len)).mul 2)).add
                ((valueK (start + len)).mul 2 + (valueK (start + len)).mul 4) :=
        entrySeedK_five6
      have h7 : entrySeedK lo start (8 * len + 7)
          = (firstLocK (indexK ((valueK (start + len)).mul 7)) lo
              ((valueK (start + len)).mul 2)).add
                ((valueK (start + len)).mul 2 + (valueK (start + len)).mul 4) :=
        entrySeedK_seven6
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ((((((((h | ⟨-, e⟩) | ⟨-, e⟩) | ⟨-, e⟩) | ⟨-, e⟩) | ⟨-, e⟩) | ⟨-, e⟩) | ⟨-, e⟩)
          | ⟨-, e⟩)
        · obtain ⟨i, hi, w, hw, hc, hs⟩ := h
          exact ⟨i, by lia, w, hw, hc, hs⟩
        · exact ⟨len, by lia, 0, by lia, hb, by rw [h0]; exact e.symm⟩
        · exact ⟨len, by lia, 1, by lia, hb, by rw [h1]; exact e.symm⟩
        · exact ⟨len, by lia, 2, by lia, hb, by rw [h2]; exact e.symm⟩
        · exact ⟨len, by lia, 3, by lia, hb, by rw [h3]; exact e.symm⟩
        · exact ⟨len, by lia, 4, by lia, hb, by rw [h4]; exact e.symm⟩
        · exact ⟨len, by lia, 5, by lia, hb, by rw [h5]; exact e.symm⟩
        · exact ⟨len, by lia, 6, by lia, hb, by rw [h6]; exact e.symm⟩
        · exact ⟨len, by lia, 7, by lia, hb, by rw [h7]; exact e.symm⟩
      · rintro ⟨i, hi, w, hw, hc, hs⟩
        rcases Nat.lt_or_ge i len with h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
            ⟨i, h, w, hw, hc, hs⟩)))))))
        · have hil : i = len := by lia
          rw [hil] at hs
          rcases (by lia : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7) with
            e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7
          · rw [e0, h0] at hs
            exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
              (Or.inr ⟨by lia, hs.symm⟩)))))))
          · rw [e1, h1] at hs
            exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by lia, hs.symm⟩))))))
          · rw [e2, h2] at hs
            exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by lia, hs.symm⟩)))))
          · rw [e3, h3] at hs
            exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by lia, hs.symm⟩))))
          · rw [e4, h4] at hs
            exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by lia, hs.symm⟩)))
          · rw [e5, h5] at hs
            exact Or.inl (Or.inl (Or.inr ⟨by lia, hs.symm⟩))
          · rw [e6, h6] at hs
            exact Or.inl (Or.inr ⟨by lia, hs.symm⟩)
          · rw [e7, h7] at hs
            exact Or.inr ⟨by lia, hs.symm⟩

/-- The wide-leaf tree removes from the window exactly what an eight-strike batch's run removes. -/
theorem segLoopSCK_eq_wtree8 {c lo start len n Wm1 seg : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 4194304) (hn : 2 ≤ n)
    (hband : ∀ i, i < len → valueK (start + i) * 4 ≤ Wm1 ∧ Wm1 < valueK (start + i) * 8) :
    segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (wtreeBatchK c lo Wm1 start len) := by
  have hz : ∀ x : Nat, Nat.ldiff x 0 = x := by
    intro x
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp
  have hrun : segLoopSCK c lo Wm1 n seg start len
      = Nat.ldiff seg (segAccLoopSK c lo Wm1 n 0 start len) := by
    have h := segLoopSCK_eq_ldiff (c := c) (lo := lo) (Wm1 := Wm1) (n := n) (seg := seg)
      (acc := 0) (start := start) (fuel := len)
    rwa [hz] at h
  rw [hrun]
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_ldiff, Nat.testBit_ldiff]
  cases hs : seg.testBit j with
  | false => rfl
  | true =>
    have hj : j ≤ Wm1 := by
      by_contra hgt
      rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia)))] at hs
      simp at hs
    have hiff : (segAccLoopSK c lo Wm1 n 0 start len).testBit j = true ↔
        (wtreeBatchK c lo Wm1 start len).testBit j = true := by
      rw [testBit_segAccLoopSK_band8 hj hn hband]
      unfold wtreeBatchK
      rw [testBit_wtreeFoldK hW hj]
    cases h1 : (segAccLoopSK c lo Wm1 n 0 start len).testBit j with
    | false =>
      cases h2 : (wtreeBatchK c lo Wm1 start len).testBit j with
      | false => rfl
      | true =>
        rw [h1, h2] at hiff
        simp at hiff
    | true =>
      rw [hiff.mp h1]

/-- One batch of the eight-strike band, settled by a tree with leaves of 262144 bits. -/
public theorem wtreeStep8 {c lo Wm1 n W start len seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hW4 : Nat.blt Wm1 4194304 = true) (hn : Nat.ble 2 n = true)
    (hlast : Nat.ble (Nat.mul (valueK (start + len)) 4) Wm1 = true)
    (hfirst : Nat.blt Wm1 (Nat.mul (valueK start) 8) = true)
    (hbatch : Nat.beq (wtreeBatchK c lo Wm1 start len) lit = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  have hWe : Wm1 + 1 = W := Nat.eq_of_beq_eq_true hWeq
  have hseg : seg < 2 ^ (Wm1 + 1) := by
    rw [hWe]
    exact lt_two_pow_of_shiftRight (Nat.eq_of_beq_eq_true hsegW)
  have hW' : Wm1 < 4194304 := Nat.le_of_ble_eq_true hW4
  have hb := Nat.eq_of_beq_eq_true hbatch
  refine Nat.beq_eq.mpr ?_
  rw [segLoopSCK_eq_wtree8 hseg hW' (Nat.le_of_ble_eq_true hn) (octave_of_tests hlast hfirst), hb,
    ldiff_eq_sub]
  exact Nat.eq_of_beq_eq_true hclear

/-! ## What the window holds

The two facts below are the arithmetic that segmentation actually adds: the local seed is the
right one, and a local offset names the number you expect. -/

/-- `firstLocK` in ordinary notation, for use in proofs. -/
public theorem firstLocK_eq {A lo m : ℕ} :
    firstLocK A lo m = (A + m - lo % m) % m := rfl

/-- The seed offset lies inside one period. -/
public theorem firstLocK_lt {A lo m : ℕ} (hm : 0 < m) : firstLocK A lo m < m := by
  rw [firstLocK_eq]
  exact Nat.mod_lt _ hm

/-- The seed offset puts the window position `lo + firstLocK A lo m` in the progression
`A, A + m, A + 2*m, …`, which is the hypothesis shape the `buildMaskK` bit characterisation in
`PrimeCert.SieveCorrect` asks for. Needs `A ≤ lo`: the window sits above the base range. -/
public theorem firstLocK_spec {A lo m : ℕ} (hm : 0 < m) (hA : A ≤ lo) :
    ∃ c, lo + firstLocK A lo m = A + m * c := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = A + m - lo % m := ⟨_, rfl⟩
  have h2 : m * (lo / m) + lo % m = lo := Nat.div_add_mod lo m
  have h3 : lo % m < m := Nat.mod_lt _ hm
  have h1 : m * (lo / m + 1) = m * (lo / m) + m := Nat.mul_succ _ _
  have h4 : m * (x / m) + x % m = x := Nat.div_add_mod x m
  have hx : firstLocK A lo m = x % m := by
    rw [firstLocK_eq, hxdef]
  have h5 : x / m ≤ lo / m + 1 := by
    have hle : m * (x / m) ≤ m * (lo / m + 1) := by lia
    exact Nat.le_of_mul_le_mul_left hle hm
  obtain ⟨c, hc⟩ : ∃ c, lo / m + 1 = x / m + c := ⟨lo / m + 1 - x / m, by lia⟩
  have h8 : m * (lo / m + 1) = m * (x / m + c) := by rw [hc]
  have h7 : m * (x / m + c) = m * (x / m) + m * c := Nat.left_distrib _ _ _
  exact ⟨c, by rw [hx]; lia⟩

/-- The number at local offset `2*k` of a window starting at `a`. -/
public theorem value_index_add {a k : ℕ} (ha : a % 6 = 1 ∨ a % 6 = 5) :
    value (index a + 2 * k) = a + 6 * k := by
  grind [value, index]

/-- A divisor's two progressions start `2 * index p + 1` wheel positions apart. A routine walking
the base sieve is at `index p` when it reaches `p`, so the second progression's index is the first
one's plus a number already in hand. -/
public theorem index_mul_seven {p : ℕ} (hp : p % 6 = 1 ∨ p % 6 = 5) :
    index (p.mul 7) = index (p.mul 5) + (index p * 2 + 1) := by
  unfold index
  rcases hp with h | h
  · obtain ⟨a, rfl⟩ : ∃ a, p = 6 * a + 1 := ⟨p / 6, by lia⟩
    lia
  · obtain ⟨a, rfl⟩ : ∃ a, p = 6 * a + 5 := ⟨p / 6, by lia⟩
    lia

/-- Taking a divisor's second strike from its first gives the same tree as deriving it from the
divisor's own second progression. -/
public theorem treeDiv2EK_eq {t : Lvl7} {lo Wm1 k : Nat} :
    treeDiv2EK t lo Wm1 k = treeDiv2K t lo Wm1 (valueK k) := by
  have hp : (value k) % 6 = 1 ∨ (value k) % 6 = 5 := coprime6_mod.mp value_coprime6
  have hpos : 0 < value k * 2 := by
    have h1 : 1 ≤ value k := by grind [value]
    lia
  have hmod : lo % (value k * 2) < value k * 2 := Nat.mod_lt _ hpos
  simp only [treeDiv2EK, treeDiv2K, valueK_eq_value, indexK_eq_index, firstLocK_eq]
  congr 1
  rw [Nat.mod_add_mod, index_mul_seven hp, index_value]
  congr 1
  lia

/-- Loop recurrence for the derived-strike fold, in the `Bool.rec` form the definition uses. -/
public theorem treeFold2EK_succ {c lo Wm1 start len : Nat} :
    treeFold2EK c lo Wm1 start (len + 1)
      = (testBitK c len).rec (treeFold2EK c lo Wm1 start len)
          (treeDiv2EK (treeFold2EK c lo Wm1 start len) lo Wm1 (start.add len)) := rfl

/-- Deriving each divisor's second strike from its first gives the batch's own tree. -/
public theorem treeFold2EK_eq {c lo Wm1 start : Nat} : ∀ {len : Nat},
    treeFold2EK c lo Wm1 start len = treeFold2K c lo Wm1 start len
  | 0 => rfl
  | _ + 1 => by
    rw [treeFold2EK_succ, treeFold2K_succ, treeFold2EK_eq, treeDiv2EK_eq]

/-- Deriving each divisor's second strike from its first gives the batch's own mask, so the
emitter may state a batch either way. -/
public theorem treeBatch2EK_eq {c lo Wm1 start len : Nat} :
    treeBatch2EK c lo Wm1 start len = treeBatch2K c lo Wm1 start len :=
  congrArg flat7 treeFold2EK_eq

/-- `treeStep2` for a batch stated with each divisor's second strike taken from its first. The
kernel checks the same window against the same mask, reaching it with one progression derived
rather than two. -/
public theorem treeStep2E {c lo Wm1 n W start len seg lit next : Nat}
    (hWeq : Nat.beq (Wm1 + 1) W = true) (hsegW : Nat.beq (seg.shiftRight W) 0 = true)
    (hW4 : Nat.blt Wm1 4194304 = true)
    (hwide : Nat.blt Wm1 (Nat.mul (valueK start) 2) = true)
    (hbatch : Nat.beq (treeBatch2EK c lo Wm1 start len) lit = true)
    (hclear : Nat.beq (Nat.sub seg (Nat.land lit seg)) next = true) :
    (segLoopSCK c lo Wm1 n seg start len).beq next = true := by
  refine treeStep2 hWeq hsegW hW4 hwide ?_ hclear
  rwa [treeBatch2EK_eq] at hbatch

/-- The completed run over the window of `W` positions from `a`, sieved by the base primes up to
`B`, in terms of `a`, `W` and `B` themselves. This is the form the correctness statements speak in
and the form `run_segment` emits alongside the numeral one, through `segRun_of`. -/
@[expose] public noncomputable def segRun (s a W B : ℕ) : ℕ :=
  segLoopK s (index a) (W - 1) (initSegK W) 1 (index B)

/-- `segRun` in the raw form the batch lemmas chain to. -/
public theorem segRun_eq {s a W B : ℕ} :
    segRun s a W B = segLoopK s (index a) (W - 1) (initSegK W) 1 (index B) := rfl

/-- The numeral form the batches produce carries over to `segRun`, given that the numerals are the
ones `a`, `W` and `B` compute to. -/
public theorem segRun_of {s a lo W wm1 B fuel b : ℕ} (hlo : Nat.beq (indexK a) lo = true)
    (hw : Nat.beq (Nat.sub W 1) wm1 = true) (hf : Nat.beq (indexK B) fuel = true)
    (h : segLoopK s lo wm1 (initSegK W) 1 fuel = b) : segRun s a W B = b := by
  have h1 : index a = lo := by
    have hb := Nat.eq_of_beq_eq_true hlo
    rwa [indexK_eq_index] at hb
  have h2 : W - 1 = wm1 := Nat.eq_of_beq_eq_true hw
  have h3 : index B = fuel := by
    have hb := Nat.eq_of_beq_eq_true hf
    rwa [indexK_eq_index] at hb
  rw [segRun_eq, h1, h2, h3]
  exact h

/-- Every surviving bit of the window names a number with no prime factor among the base primes,
proved by `segmentSound_of`. One direction only: a cleared bit is left unclassified, so this gives
primality of the survivors exactly when the window sits below the square of the base bound. -/
@[expose] public def SegmentSound (s B a W : ℕ) : Prop :=
  ∀ j < W, (segLoopK s (index a) (W - 1) (initSegK W) 1 (index B)).testBit j →
    ∀ q ≤ B, q.Prime → ¬ q ∣ value (index a + j)

/-! ## Correctness of a segment

A surviving bit names a number with no prime factor among the base primes. The argument: for a
prime `q` dividing the number at position `j`, the run reaches `q`'s own base index with `q`'s bit
set in the base sieve, the mask built there covers `j`, and every later step only clears bits. -/

/-- A step clears exactly the bits of the mask. -/
public theorem testBit_segMarkK {seg p lo Wm1 j : Nat} :
    (segMarkK seg p lo Wm1).testBit j
      = (seg.testBit j && !(buildMaskK p Wm1 (firstLocK (indexK (p * 5)) lo (p * 2))
          (firstLocK (indexK (p * 7)) lo (p * 2)) 32).testBit j) := by
  have hraw : segMarkK seg p lo Wm1
      = seg - (seg &&& buildMaskK p Wm1 (firstLocK (indexK (p * 5)) lo (p * 2))
          (firstLocK (indexK (p * 7)) lo (p * 2)) 32) := rfl
  rw [hraw, Nat.sub_and_eq_ldiff, Nat.testBit_ldiff]

/-- A run only clears bits: a bit set at the end was set at the start. -/
public theorem testBit_of_testBit_segLoopK {s lo Wm1 seg start fuel j : Nat}
    (h : (segLoopK s lo Wm1 seg start fuel).testBit j) : seg.testBit j := by
  induction fuel with
  | zero => exact h
  | succ n ih =>
    rw [segLoopK_succ] at h
    cases hb : testBitK s (start + n) with
    | false =>
      rw [hb] at h
      exact ih h
    | true =>
      rw [hb, testBit_segMarkK, Bool.and_eq_true] at h
      exact ih h.1

/-- The offset of a multiple of `p` inside the window lies in one of the two progressions the mask
draws, so the mask covers it. -/
public theorem testBit_mask_of_dvd {q lo j c X : Nat} (hq : 0 < q)
    (hX : X ≤ lo) (hstep : lo + j = X + 2 * q * c) :
    firstLocK X lo (q * 2) ≤ j ∧ 2 * q ∣ j - firstLocK X lo (q * 2) := by
  have hm : 0 < q * 2 := by lia
  obtain ⟨c0, hc0⟩ := firstLocK_spec (A := X) (lo := lo) hm hX
  have hA : firstLocK X lo (q * 2) < q * 2 := firstLocK_lt hm
  have hcc : c0 ≤ c := by
    by_contra hlt
    have h1 : c + 1 ≤ c0 := by lia
    have h2 : q * 2 * (c + 1) ≤ q * 2 * c0 := Nat.mul_le_mul_left _ h1
    have h3 : q * 2 * (c + 1) = q * 2 * c + q * 2 := by rw [Nat.mul_add, Nat.mul_one]
    lia
  have hsplit : q * 2 * c = q * 2 * c0 + q * 2 * (c - c0) := by
    rw [← Nat.mul_add]
    congr 1
    lia
  exact ⟨by lia, ⟨c - c0, by lia⟩⟩

/-- A run that passes an index whose base bit is set, with a mask covering `j`, leaves bit `j`
clear. -/
public theorem not_testBit_segLoopK {s lo Wm1 seg start fuel t j : Nat}
    (htf : t < start + fuel) (hts : start ≤ t) (hbit : testBitK s t = true)
    (hmask : (buildMaskK (valueK t) Wm1 (firstLocK (indexK (valueK t * 5)) lo (valueK t * 2))
      (firstLocK (indexK (valueK t * 7)) lo (valueK t * 2)) 32).testBit j = true) :
    (segLoopK s lo Wm1 seg start fuel).testBit j = false := by
  induction fuel with
  | zero => lia
  | succ n ih =>
    rw [segLoopK_succ]
    cases hb : testBitK s (start + n) with
    | false =>
      refine ih ?_
      rcases Nat.lt_or_ge t (start + n) with hlt | hge
      · exact hlt
      · have ht : start + n = t := by lia
        rw [ht, hbit] at hb
        exact absurd hb (by simp)
    | true =>
      rw [testBit_segMarkK]
      rcases Nat.lt_or_ge t (start + n) with hlt | hge
      · rw [ih hlt]
        simp
      · have ht : start + n = t := by lia
        rw [ht, hmask]
        simp

set_option maxHeartbeats 1000000 in
-- The proof carries a dozen arithmetic side conditions about `index`, `value` and divisibility,
-- each closed by `lia` against the whole context, which together pass the default limit.
/-- Every surviving bit of a completed run names a number with no prime factor up to `B`. -/
public theorem segmentSound_of {s B a W : Nat} (hs : IsSieve B s)
    (ha : a % 6 = 1 ∨ a % 6 = 5) (hW : W - 1 < 2 ^ 32) (hB1 : 1 ≤ B) (h7B : 7 * B ≤ a) :
    SegmentSound s B a W := by
  intro j hj hbit q hqB hq hdvd
  have hlo : value (index a) = a := value_index ha
  have hjval : a ≤ value (index a + j) := by
    have := value_strictMono.monotone (Nat.le_add_right (index a) j)
    lia
  have hcop : Nat.Coprime (value (index a + j)) 6 := value_coprime6
  have hqcop : Nat.Coprime q 6 := Nat.Coprime.coprime_dvd_left hdvd hcop
  have hq6 : q % 6 = 1 ∨ q % 6 = 5 := coprime6_mod.mp hqcop
  have hq2 : 2 ≤ q := hq.two_le
  have hq5 : 5 ≤ q := by lia
  obtain ⟨k, hk⟩ := hdvd
  have hkcop : Nat.Coprime k 6 := Nat.Coprime.coprime_dvd_left ⟨q, by lia⟩ hcop
  have hk6 : k % 6 = 1 ∨ k % 6 = 5 := coprime6_mod.mp hkcop
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have h1 : k ≤ 1 := by lia
    have h2 : q * k ≤ q * 1 := Nat.mul_le_mul_left q h1
    lia
  have hk5 : 5 ≤ k := by lia
  -- the base index of `q`, and its bit in the base sieve
  have hvq : value (index q) = q := value_index hq6
  have ht0 : index q ≠ 0 := by
    unfold index
    lia
  have htB : index q ≤ index B := by
    unfold index
    lia
  have hbitq : s.testBit (index q) := by
    have hle : value (index q) ≤ B := by lia
    have hpr : (value (index q)).Prime := by rwa [hvq]
    exact (hs (index q) ht0 hle).mpr hpr
  -- the mask built at `q` covers `j`
  have hmask : (buildMaskK q (W - 1) (firstLocK (indexK (q * 5)) (index a) (q * 2))
      (firstLocK (indexK (q * 7)) (index a) (q * 2)) 32).testBit j := by
    rw [testBit_buildMaskK (by lia) (by lia) hW]
    rcases hk6 with h1 | h5
    · right
      obtain ⟨c, rfl⟩ : ∃ c, k = 7 + 6 * c := ⟨(k - 7) / 6, by lia⟩
      have hval : value (index a + j) = value (index (q * 7)) + 6 * (q * c) := by
        rw [value_startB hq6]
        lia
      have hstep : index a + j = index (q * 7) + 2 * q * c := by
        have := value_add_two_mul (k := index (q * 7)) (m := q * c)
        have heq : value (index a + j) = value (index (q * 7) + 2 * (q * c)) := by lia
        have := value_strictMono.injective heq
        lia
      have h7q : q * 7 ≤ B * 7 := Nat.mul_le_mul_right 7 hqB
      have hX : index (q * 7) ≤ index a := by
        unfold index
        lia
      simpa using testBit_mask_of_dvd (q := q) (by lia) hX hstep
    · left
      obtain ⟨c, rfl⟩ : ∃ c, k = 5 + 6 * c := ⟨(k - 5) / 6, by lia⟩
      have hval : value (index a + j) = value (index (q * 5)) + 6 * (q * c) := by
        rw [value_startA hq6]
        lia
      have hstep : index a + j = index (q * 5) + 2 * q * c := by
        have := value_add_two_mul (k := index (q * 5)) (m := q * c)
        have heq : value (index a + j) = value (index (q * 5) + 2 * (q * c)) := by lia
        have := value_strictMono.injective heq
        lia
      have h5q : q * 5 ≤ B * 7 := by
        have := Nat.mul_le_mul_right 5 hqB
        lia
      have hX : index (q * 5) ≤ index a := by
        unfold index
        lia
      simpa using testBit_mask_of_dvd (q := q) (by lia) hX hstep
  -- the run passes `q`'s index, so the bit is clear at the end
  have hbitK : testBitK s (index q) = true := by
    rw [testBitK_eq_testBit]
    exact hbitq
  have hmaskK : (buildMaskK (valueK (index q)) (W - 1)
      (firstLocK (indexK (valueK (index q) * 5)) (index a) (valueK (index q) * 2))
      (firstLocK (indexK (valueK (index q) * 7)) (index a) (valueK (index q) * 2)) 32).testBit j
      = true := by
    rw [valueK_eq_value, hvq, indexK_eq_index]
    exact hmask
  have hclear := not_testBit_segLoopK (s := s) (lo := index a) (Wm1 := W - 1)
    (seg := initSegK W) (start := 1) (fuel := index B) (t := index q) (j := j)
    (by lia) (by lia) hbitK hmaskK
  rw [hclear] at hbit
  exact absurd hbit (by simp)

/-! ## Completeness of a segment

The converse direction: a cleared bit is cleared for a reason. Each step clears only the mask of
one base prime, and a mask bit of `p` sits at an offset whose number is a multiple of `p`, so a
number with no prime factor up to `B` keeps its bit through the whole run. -/

/-- A mask bit of `p` in the window names a multiple of `p`. -/
public theorem dvd_of_testBit_mask {p lo Wm1 j : Nat} (hp6 : p % 6 = 1 ∨ p % 6 = 5)
    (hp5 : 5 ≤ p) (hlo : index (p * 7) ≤ lo) (hj : j ≤ Wm1) (hW : Wm1 < 2 ^ 32)
    (h : (buildMaskK p Wm1 (firstLocK (index (p * 5)) lo (p * 2))
      (firstLocK (index (p * 7)) lo (p * 2)) 32).testBit j = true) :
    p ∣ value (lo + j) := by
  have hm : 0 < p * 2 := by lia
  have h57 : index (p * 5) ≤ index (p * 7) := by
    unfold index
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (by lia) 1)
  have h5lo : index (p * 5) ≤ lo := by lia
  have h5 : value (index (p * 5)) = p * 5 := value_index (by lia)
  have h7 : value (index (p * 7)) = p * 7 := value_index (by lia)
  rw [testBit_buildMaskK (by lia) hj hW] at h
  rcases h with ⟨hle, d, hd⟩ | ⟨hle, d, hd⟩
  · obtain ⟨c, hc⟩ := firstLocK_spec (A := index (p * 5)) (lo := lo) hm h5lo
    have hsum : lo + j = index (p * 5) + 2 * (p * (c + d)) := by lia
    have hval : value (lo + j) = p * 5 + 6 * (p * (c + d)) := by
      rw [hsum, value_add_two_mul, h5]
    exact ⟨5 + 6 * (c + d), by lia⟩
  · obtain ⟨c, hc⟩ := firstLocK_spec (A := index (p * 7)) (lo := lo) hm hlo
    have hsum : lo + j = index (p * 7) + 2 * (p * (c + d)) := by lia
    have hval : value (lo + j) = p * 7 + 6 * (p * (c + d)) := by
      rw [hsum, value_add_two_mul, h7]
    exact ⟨7 + 6 * (c + d), by lia⟩

/-- A run whose every step misses `j` leaves bit `j` as it found it. -/
public theorem testBit_segLoopK_of {s lo Wm1 seg start fuel j : Nat} (hseg : seg.testBit j = true)
    (hno : ∀ t, start ≤ t → t < start + fuel → testBitK s t = true →
      (buildMaskK (valueK t) Wm1 (firstLocK (indexK (valueK t * 5)) lo (valueK t * 2))
        (firstLocK (indexK (valueK t * 7)) lo (valueK t * 2)) 32).testBit j = false) :
    (segLoopK s lo Wm1 seg start fuel).testBit j = true := by
  induction fuel with
  | zero => exact hseg
  | succ n ih =>
    have ihn := ih fun t h1 h2 h3 => hno t h1 (by lia) h3
    rw [segLoopK_succ]
    cases hb : testBitK s (start + n) with
    | false => exact ihn
    | true =>
      rw [testBit_segMarkK, ihn, hno (start + n) (by lia) (by lia) hb]
      simp

/-- Every bit below `W` of the window a run starts from is set. -/
public theorem testBit_initSegK {W j : Nat} (hj : j < W) : (initSegK W).testBit j = true := by
  have hs1 : initSegK W = 2 ^ W - 1 := by
    unfold initSegK
    have hsl : Nat.shiftLeft 1 W = 1 <<< W := rfl
    have h : (1 : Nat) <<< W = 2 ^ W := by rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [hsl, h]
    rfl
  rw [hs1, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

/-- The bit of a number with no prime factor up to `B` survives the run. -/
@[expose] public def SegmentComplete (s B a W : Nat) : Prop :=
  ∀ j < W, (∀ q ≤ B, q.Prime → ¬ q ∣ value (index a + j)) →
    (segLoopK s (index a) (W - 1) (initSegK W) 1 (index B)).testBit j = true

set_option maxHeartbeats 1000000 in
-- As in `segmentSound_of`, the divisibility side conditions are closed against the whole context
-- and together pass the default limit.
/-- Every bit a completed run clears names a number with a prime factor up to `B`, stated as its
contrapositive. `B % 6` is 1 or 5 so that the run's last base index is `B` itself. -/
public theorem segmentComplete_of {s B a W : Nat} (hs : IsSieve B s)
    (hB6 : B % 6 = 1 ∨ B % 6 = 5) (hW : W - 1 < 2 ^ 32)
    (h7B : 7 * B ≤ a) : SegmentComplete s B a W := by
  intro j hj hno
  have hvB : value (index B) = B := value_index hB6
  refine testBit_segLoopK_of (testBit_initSegK hj) ?_
  · intro t h1 h2 hbit
    by_contra hmask
    rw [Bool.not_eq_false] at hmask
    rw [valueK_eq_value, indexK_eq_index] at hmask
    have ht0 : t ≠ 0 := Nat.one_le_iff_ne_zero.mp h1
    have ht5 : 5 ≤ value t := five_le_value ht0
    have h2' : t < index B + 1 := by rw [Nat.add_comm] at h2; exact h2
    have hmono := value_strictMono.monotone (Nat.lt_succ_iff.mp h2')
    have htB : value t ≤ B := by rw [hvB] at hmono; exact hmono
    rw [testBitK_eq_testBit] at hbit
    have hprime : (value t).Prime := (hs t ht0 htB).mp hbit
    have hmul : value t * 7 ≤ a :=
      calc value t * 7 = 7 * value t := Nat.mul_comm _ _
        _ ≤ 7 * B := Nat.mul_le_mul_left 7 htB
        _ ≤ a := h7B
    have hlo : index (value t * 7) ≤ index a := by
      unfold index
      exact Nat.div_le_div_right (Nat.sub_le_sub_right hmul 1)
    exact hno (value t) htB hprime
      (dvd_of_testBit_mask (value_mod6 t) ht5 hlo (Nat.le_sub_one_of_lt hj) hW hmask)

/-! ## A product of the values a window still holds

Groundwork for a certificate that sieves by one `Nat.gcd` per slice in place of a mask per divisor.
A window of 4194304 bits costs about 65.5 s of kernel today; the gcd shape was priced on
2026-11-12 at 1.85 s of kernel and 2.0 s of emitter per window, which is why it is worth proving
rather than guessing at.

The arithmetic those timings measured is sound already, since `Nat.gcd` is on the kernel's fast
path. What was missing is the bridge from a coprimality statement to the window, and that is what
these give, ending at `segLoopK_eq_self_of_blocks`: a whole range of divisors leaves the window
alone, so not one of their masks need be built.

A window's live product cannot be taken whole — 4194304 bits of survivors multiply to a number far
past anything worth stating — so the emitter takes one product per 65536-bit slice and states one
`Nat.gcd` for each. The hypotheses below are in that shape deliberately. -/

/-- The product of the values at the live bits of `seg` in the block of `n` bits starting at
`off`, the window's values counted from `lo`. -/
@[expose] public noncomputable def prodLiveFromK (seg lo off n : Nat) : Nat :=
  n.rec 1 fun i acc =>
    (testBitK seg (off.add i)).rec acc (acc.mul (valueK (lo.add (off.add i))))

/-- A live value in a block divides that block's product. -/
public theorem dvd_prodLiveFromK {seg lo off n i : Nat} (hi : i < n)
    (h : testBitK seg (off + i) = true) :
    valueK (lo + (off + i)) ∣ prodLiveFromK seg lo off n := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hstep : prodLiveFromK seg lo off (n + 1)
        = (testBitK seg (off.add n)).rec (prodLiveFromK seg lo off n)
            ((prodLiveFromK seg lo off n).mul (valueK (lo.add (off.add n)))) := rfl
    rw [hstep]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · have hd := ih hlt
      cases hb : testBitK seg (off.add n) with
      | false => simpa using hd
      | true => exact Dvd.dvd.mul_right hd _
    · subst heq
      have h' : testBitK seg (off.add i) = true := h
      rw [h']
      exact Dvd.dvd.mul_left dvd_rfl _

/-- No divisor of `P` divides the value at a live position, given one coprimality to `P` per block
and blocks covering the window. This is what the gcd buys: every divisor of `P` ruled out at every
live position at once. -/
public theorem not_dvd_of_blocks {seg lo Wm1 p P bs nb j : Nat}
    (hbs : 0 < bs) (hcover : Wm1 + 1 ≤ nb * bs) (hp : 1 < p) (hpP : p ∣ P)
    (hgcd : ∀ k, k < nb → Nat.gcd (prodLiveFromK seg lo (k * bs) bs) P = 1)
    (hj : j ≤ Wm1) (hlive : testBitK seg j = true) : ¬ p ∣ valueK (lo + j) := by
  intro hdvd
  -- The block holding `j`, and its offset within that block.
  have hk : j / bs < nb := by
    by_contra hc
    have hle : nb * bs ≤ (j / bs) * bs := Nat.mul_le_mul_right bs (by omega)
    have hjd : (j / bs) * bs ≤ j := Nat.div_mul_le_self j bs
    omega
  have hr : j % bs < bs := Nat.mod_lt _ hbs
  have hsplit : (j / bs) * bs + j % bs = j := Nat.div_add_mod' j bs
  have hlive' : testBitK seg ((j / bs) * bs + j % bs) = true := by rw [hsplit]; exact hlive
  have hd : valueK (lo + ((j / bs) * bs + j % bs)) ∣ prodLiveFromK seg lo ((j / bs) * bs) bs :=
    dvd_prodLiveFromK hr hlive'
  rw [hsplit] at hd
  have h2 : p ∣ Nat.gcd (prodLiveFromK seg lo ((j / bs) * bs) bs) P :=
    Nat.dvd_gcd (hdvd.trans hd) hpP
  rw [hgcd _ hk] at h2
  have := Nat.le_of_dvd Nat.one_pos h2
  omega

/-- A divisor ruled out at every live position leaves the window exactly as it was, so its mask
need never be built. -/
public theorem segMarkK_eq_self_of_not_dvd {seg lo Wm1 p : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 2 ^ 32)
    (hp6 : p % 6 = 1 ∨ p % 6 = 5) (hp5 : 5 ≤ p) (hlo : index (p * 7) ≤ lo)
    (hnd : ∀ j, j ≤ Wm1 → testBitK seg j = true → ¬ p ∣ valueK (lo + j)) :
    segMarkK seg p lo Wm1 = seg := by
  -- Generalised over the mask, so the long term is written once and the content stands out: a
  -- mask that is clear wherever the window is live meets the window in nothing.
  have key : ∀ M : Nat, (∀ j, j ≤ Wm1 → Nat.testBit seg j = true → M.testBit j = false) →
      seg.land M = 0 := by
    intro M hM
    have hland : seg.land M = seg &&& M := rfl
    rw [hland]
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hj : j ≤ Wm1
    · by_cases hs : Nat.testBit seg j = true
      · rw [hM j hj hs, Bool.and_false]
      · simp only [Bool.not_eq_true] at hs
        rw [hs, Bool.false_and]
    · have hlt : seg < 2 ^ j :=
        Nat.lt_of_lt_of_le hseg (Nat.pow_le_pow_right (by lia) (by lia))
      rw [Nat.testBit_eq_false_of_lt hlt, Bool.false_and]
  have hzero : seg.land (buildMaskK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
      (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 32) = 0 := by
    refine key _ fun j hj hs => ?_
    have hlive : testBitK seg j = true := by rw [testBitK_eq_testBit]; exact hs
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    exact hnd j hj hlive (dvd_of_testBit_mask hp6 hp5 hlo hj hW hc)
  have hsub : seg.sub (seg.land (buildMaskK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
      (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 32))
      = seg - seg.land (buildMaskK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
        (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) 32) := rfl
  rw [segMarkK, hsub, hzero, Nat.sub_zero]

/-- **The certificate.** A whole range of divisors, each dividing `P`, leaves the window alone,
given one coprimality to `P` per block of the window: one `Nat.gcd` a block in place of every mask
the range would have built. -/
public theorem segLoopK_eq_self_of_blocks {s lo Wm1 seg start fuel P bs nb : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 2 ^ 32)
    (hbs : 0 < bs) (hcover : Wm1 + 1 ≤ nb * bs)
    (hgcd : ∀ k, k < nb → Nat.gcd (prodLiveFromK seg lo (k * bs) bs) P = 1)
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
      exact segMarkK_eq_self_of_not_dvd hseg hW h6 h5 hlo
        fun j hj hlive => not_dvd_of_blocks hbs hcover (by lia) hP hgcd hj hlive

public theorem valueK_mod6 (k : Nat) : valueK k % 6 = 1 ∨ valueK k % 6 = 5 := by
  rw [valueK_eq_add]
  omega

public theorem five_le_valueK {k : Nat} (hk : k ≠ 0) : 5 ≤ valueK k := by
  rw [valueK_eq_add]
  omega

/-- The certificate with `P` taken as the product of the range's own values, which is what the
emitter would build anyway, so divisibility costs nothing to establish. What is left for the
emitter is the window starting above each divisor's seventh multiple, and the gcds themselves. -/
public theorem segLoopK_eq_self_of_range {s lo Wm1 seg start fuel bs nb : Nat}
    (hseg : seg < 2 ^ (Wm1 + 1)) (hW : Wm1 < 2 ^ 32)
    (hbs : 0 < bs) (hcover : Wm1 + 1 ≤ nb * bs) (hstart : start ≠ 0)
    (hgcd : ∀ k, k < nb →
      Nat.gcd (prodLiveFromK seg lo (k * bs) bs) (prodLiveFromK s 0 start fuel) = 1)
    (hlo : ∀ i, i < fuel → testBitK s (start + i) = true →
      index (valueK (start + i) * 7) ≤ lo) :
    segLoopK s lo Wm1 seg start fuel = seg := by
  refine segLoopK_eq_self_of_blocks hseg hW hbs hcover hgcd fun i hi hbit => ?_
  refine ⟨valueK_mod6 _, five_le_valueK (by omega), hlo i hi hbit, ?_⟩
  have hd := dvd_prodLiveFromK (seg := s) (lo := 0) (off := start) (n := fuel) hi hbit
  rwa [Nat.zero_add] at hd

/-! ## Compiled twins

Executable copies of the definitions above, used by `run_segment` to compute the batch literals.
The kernel checks each batch equation, so a twin that disagreed would make `run_segment` fail.

All but the two below live in the `SieveEmit` library, which the lakefile precompiles, so that an
elaborator calling them runs compiled code rather than the interpreter. These two stay because
they call `buildMask`, which is a kernel definition of this file. -/

open SieveEmit

meta def segMark (seg p lo Wm1 : Nat) : Nat :=
  seg - (seg &&& buildMask p Wm1 (firstLoc (index (p * 5)) lo (p * 2))
    (firstLoc (index (p * 7)) lo (p * 2)) 32)

meta def segLoop (s lo Wm1 seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in setBitsLow (s >>> start) fuel do
    b := segMark b (value (start + i)) lo Wm1
  return b

/-! ## The `run_segment` command -/

open Lean Elab Command Meta

/-- The statement `Nat.beq a b = true`. -/
meta def mkSegBeqTrue (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) a b) (mkConst ``Bool.true)

/-- The application `segLoopK s lo Wm1 seg start len`, with `start` and `len` as literals. -/
meta def mkSegLoopK (sE loE wE segE : Expr) (start len : Nat) : Expr :=
  mkAppN (mkConst ``segLoopK) #[sE, loE, wE, segE, mkRawNatLit start, mkRawNatLit len]

/-- Batch length as a function of where the batch starts: short batches over the small primes,
whose masks are grown by doubling and are the widest the kernel holds at once, and long batches
over the large primes, whose masks are two bits. Each batch also leaves one window-sized literal
in the environment for the file's life, so the long end keeps that count down. -/
meta def batchLen (start : Nat) : Nat :=
  if start < 20000 then 256
  else if start < 300000 then 512
  else if start < 700000 then 768
  else 3072

/-- `batchLen` with a shorter run over the large primes. A batch holds about 869 KB per prime while
its theorem is checked, against one window-sized literal, 512 KB, per batch in the environment for
the file's life, so the two terms trade off and 3072 was measured against 8192 rather than
reasoned. -/
meta def batchLenWide (start : Nat) : Nat :=
  if start < 20000 then 256
  else if start < 300000 then 512
  else if start < 700000 then 768
  else 1536

/-- `batchLen` with a longer run over the smallest divisors. The schedule's four tiers have been
tested one at a time: `batchLenWide` moves the top tier and `batchLenMid` the two middle ones, both
measured on 2026-11-12. This moves the bottom tier, 256 to 1024 below base index 20000, which is
the only one never varied on its own. Those are the densest masks in the run and they sit in the
masked band, about 44 s of a window's 150. -/
meta def batchLenLow (start : Nat) : Nat :=
  if start < 20000 then 1024
  else if start < 300000 then 512
  else if start < 700000 then 768
  else 3072

/-- The same four lengths, on boundaries that follow the bands rather than cutting across them.

`batchLen`'s tiers break at 20000, 300000 and 700000, while the bands break at `index (Wm1 / 8)`,
`index (Wm1 / 4)` and `index (Wm1 / 2)` — at a 4194304 window, 174762, 349524 and 699050. Only the
last pair nearly agree. So today the masked band spans two tiers, the eight-record band spans two
more, and no band is given a single length. This gives each band one, which is what tuning a band
at a time assumes it already has. Taken from `Wm1` rather than written as literals, so it is right
at any width. -/
meta def batchLenBand (wm1 start : Nat) : Nat :=
  if start < index (wm1 / 8) then 256
  else if start < index (wm1 / 4) then 512
  else if start < index (wm1 / 2) then 768
  else 3072

/-- `batchLen` with longer batches over the two middle bands, which hold the divisors striking the
window four or eight times and span wheel indices of about 174762 to 699050. The shorter tiers
there were set when four files shared a runner; two files now hold 7.67 GB summed. -/
meta def batchLenMid (start : Nat) : Nat :=
  if start < 20000 then 256
  else if start < 174762 then 512
  else if start < 700000 then 4096
  else 3072

/-- Add a theorem declaration with the given statement and proof term. -/
meta def addSegThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Sieve the window of `W` wheel positions starting at the number `a` by the base primes held in
the bitset `baseLit`, scanning `fuel` base indices in batches of `len`. Emits
`ns.segBits_{a}_{W}_{fuel}_{len} : Nat` and `ns.segEq_{a}_{W}_{fuel}_{len} : segLoopK … =
segBits_…`, the latter chained from one kernel-checked `Nat.beq` lemma per batch. `ns` is the
namespace the call sits in, so the same window can be built in two modules without a clash. -/
public meta def runSegment (ns baseLit : Name) (a W fuel len : Nat) : MetaM Unit := do
  if a % 6 ≠ 1 && a % 6 ≠ 5 then
    throwError "run_segment: the window start {a} is not 1 or 5 modulo 6"
  if W = 0 then throwError "run_segment: the window is empty"
  let env ← getEnv
  let some info := env.find? baseLit | throwError "run_segment: no base sieve {baseLit}"
  let some sVal := info.value?.bind Expr.rawNatLit?
    | throwError "run_segment: the base sieve {baseLit} is not a numeral"
  let lo := index a
  let wm1 := W - 1
  let step0 := Nat.max 1 len
  let sE := mkConst baseLit
  let loE := mkRawNatLit lo
  let wE := mkRawNatLit wm1
  -- Marking is clamped: seeds that fall outside the window are dropped, a divisor too large to
  -- repeat skips the doubling rounds altogether, and a batch that hits nothing is not subtracted
  -- from. `segLoopCK_eq_stride` proves this loop equal to `segLoopK`, so `segEq_of_clamped` turns
  -- the chain back into a statement about `segLoopK` and the theorem this command emits is
  -- unchanged. Measured 2026-11-12 on a fresh c7i.8xlarge, `run.sh 3`, load about 1, at
  -- W = 4194304 and 333333 divisors: kernel 85.98-86.76 s against 89.40-89.61 unclamped and
  -- processor 130.6-131.9 against 135.7-136.1, ranges not overlapping, peak unchanged at 1.9 GB.
  -- `run_segment_variant 0` is the unclamped loop, kept as the arm this was measured against.
  let rounds := Nat.log2 wm1 + 1
  let nE := mkRawNatLit rounds
  let initE := mkApp (mkConst ``initSegK) (mkRawNatLit W)
  let loopE (segE : Expr) (start n : Nat) : Expr :=
    mkAppN (mkConst ``segLoopCK) #[sE, loE, wE, nE, segE, mkRawNatLit start, mkRawNatLit n]
  let lhsLoop := loopE initE 1 fuel
  let tag := s!"{a}_{W}_{fuel}_{step0}"
  let parent := ns ++ Name.mkSimple s!"segEq_{tag}"
  let litName := ns ++ Name.mkSimple s!"segBits_{tag}"
  let mut bits := initSeg W
  let mut bitsE := initE
  let mut proof := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[Nat.mkType, lhsLoop]
  for i in [0:(fuel + step0 - 1) / step0] do
    let start := 1 + i * step0
    let owed := fuel - i * step0
    let stepN := Nat.min step0 owed
    let next := segLoopC sVal lo wm1 rounds bits start stepN
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
    addSegThm stepName
      (mkSegBeqTrue (loopE bitsE start stepN) (mkRawNatLit next)) Lean.reflBoolTrue
    proof := if owed == stepN then
        mkAppN (mkConst ``segLoopCK_last)
          #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start,
            mkRawNatLit stepN, proof, mkConst stepName]
      else
        mkAppN (mkConst ``segLoopCK_chain)
          #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start,
            mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst stepName]
    bits := next
    bitsE := mkRawNatLit next
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := Nat.mkType,
      value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
  addSegThm parent (mkNatEq (mkSegLoopK sE loE wE initE 1 fuel) (mkConst litName))
    (mkAppN (mkConst ``segEq_of_clamped)
      #[sE, loE, mkRawNatLit W, wE, nE, mkRawNatLit fuel, mkRawNatLit bits,
        Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, proof])
  let bVal := value fuel
  addSegThm (ns ++ Name.mkSimple s!"segEqI_{a}_{W}_{fuel}_{step0}")
    (mkNatEq (mkAppN (mkConst ``segRun)
        #[sE, mkRawNatLit a, mkRawNatLit W, mkRawNatLit bVal]) (mkConst litName))
    (mkAppN (mkConst ``segRun_of)
      #[sE, mkRawNatLit a, loE, mkRawNatLit W, wE, mkRawNatLit bVal, mkRawNatLit fuel,
        mkConst litName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
        mkConst parent])

/-- `runSegment` with a choice of loop and of batch assembly, for timing the draft variants
against each other. The loop is `mode % 4`: 0 is `segLoopK`, 1 is `segLoopCK`, 2 is `segLoopSK`
and 3 is `segLoopSCK`. Loops 2 and 3 emit one lemma checking the slice of the base sieve
(`…chunk_{i}`) per batch as well as the batch lemma (`…step_{i}`). Modes 0 to 3 assemble the
batches as one chain, modes 4 to 7 as a tree: each batch becomes a `…leaf_{i}` equation and each
`…join_{level}_{j}` combines two neighbours. Every mode ends at
`ns.segEqV_{tag} : segLoopK … = ns.segBitsV_{tag}`, the clamped loops through `segEq_of_clamped`.
Modes 0 to 7 compute the batch literals with the `segLoop` twin and modes 8 to 15 with the
`segLoopC` twin, the same eight assemblies otherwise, so the pair `m` and `m + 8` differs in the
command's own computation alone. Mode 16 joins each batch's masks into a running total and clears
the window once at the end, in place of clearing it per prime; it uses slices, the `segLoopC` twin
and a chain, so mode 11 is the arm to compare it against. -/
meta def runSegmentV (ns baseLit : Name) (mode a W fuel len : Nat)
    (prodNames : Bool := false) : MetaM Unit := do
  if a % 6 ≠ 1 && a % 6 ≠ 5 then
    throwError "run_segment_variant: the window start {a} is not 1 or 5 modulo 6"
  if W = 0 then throwError "run_segment_variant: the window is empty"
  if mode > 86 then throwError "run_segment_variant: mode {mode} is not 0 to 86"
  if mode == 72 && len > 4096 then
    throwError "run_segment_variant: mode 72 spends a record bit on the flag, so a batch holds \
      4096 positions, not {len}"
  if (mode == 28 || mode == 34 || mode == 37 || mode == 38 || mode == 39 || mode == 40
        || mode == 45 || mode == 53 || mode == 54 || mode == 55 || mode == 57 || mode == 58
        || mode == 59 || mode == 60 || mode == 61 || mode == 62 || mode == 63
        || mode == 64 || mode == 65 || mode == 67 || mode == 68 || mode == 71)
      && len > 8192 then
    throwError "run_segment_variant: a record is 16 bits, of which three name which strike, so a \
      sorted batch holds at most 8192 positions, not {len}"
  let env ← getEnv
  let some info := env.find? baseLit
    | throwError "run_segment_variant: no base sieve {baseLit}"
  let some sVal := info.value?.bind Expr.rawNatLit?
    | throwError "run_segment_variant: the base sieve {baseLit} is not a numeral"
  -- Mode 38 is mode 28 with a batch's two theorems emitted as one: the sorted-batch proof goes
  -- straight into `segLoopK_batch` rather than through a named intermediate. Same statements
  -- reaching the chain, one declaration a batch fewer, which is an elaboration cost rather than a
  -- kernel one.
  let fold := mode == 38
  -- Mode 39 sorts every batch exactly as mode 28 does and then throws the sorted records away,
  -- settling the batch the plain way instead. Its statements are mode 20's, so it is sound; what
  -- it isolates is `stripeSort`'s own cost, the sorted shape's elaboration bill minus the emitted
  -- records.
  let sortOnly := mode == 39
  -- Mode 45 is mode 28 with the widest band routed through the tree: the kernel derives each
  -- divisor's two strikes and dispatches them by the bits of the leaf number, so the batch owes
  -- one equation against the assembled mask instead of a record list, a tally and a clear.
  -- Mode 53 is mode 45 with the tree's leaves at 262144 bits rather than 65536. Mode 54 sends all
  -- three bands through that tree, so no batch of the run uses sorted records.
  -- Mode 58 is mode 45 with each divisor's second strike taken from its first, which
  -- `index_mul_seven` puts `2 * index p + 1` wheel positions along from it.
  let derivedStrike := mode == 58
  -- Mode 59 is mode 45 with one extra equation per widest-band batch, counting the divisors the
  -- batch names by the same walk, so the walk can be priced apart from the strikes.
  let walkProbe := mode == 59
  -- Mode 60 is mode 45 with one extra equation per widest-band batch, summing the strike
  -- positions that batch's divisors give, so the seed arithmetic can be priced apart from the
  -- dispatch of each strike into its leaf.
  let seedProbe := mode == 60
  -- Mode 61 is mode 45 with one extra equation per widest-band batch, joining that batch's
  -- strikes in leaf order so a leaf is built whole and joined once. Against mode 60 it prices
  -- that grouping against the per-strike descent through the tree.
  let bucketProbe := mode == 61
  -- Modes 62 and 63 add, per batch of the smallest band, one equation joining that batch's masks,
  -- built by doubling and by multiplication respectively, so the pair prices the construction.
  let maskProbe := mode == 62
  let maskMulProbe := mode == 63
  -- Modes 64 and 65 add, per batch of the smallest band, one equation joining the masks of two
  -- consecutive windows: 64 builds both by doubling, 65 takes the second from the first by a
  -- shift. The pair prices sharing a divisor's construction across windows.
  let twoWinProbe := mode == 64
  let twoWinShiftProbe := mode == 65
  let tree := mode == 45 || mode == 53 || mode == 54 || derivedStrike || walkProbe || seedProbe
    || bucketProbe
  let wideLeaf := mode == 53 || mode == 54
  let allTree := mode == 54
  -- Mode 55 is mode 28 with the twin's marking pass kept, so a pair of runs prices taking the
  -- next window from the batch's own mask instead.
  let twoPass := mode == 55
  -- Mode 56 is mode 28 with every batch settled by the marked shape, whose mask is built by
  -- doubling rather than by sorting the batch's strikes into records.
  let marked := mode == 56
  -- Mode 57 is mode 28 with the two middle bands run in batches of 4096 rather than 512 and 768.
  let midLong := mode == 57
  -- Mode 73 is mode 28 with every batch the length the call gives, rather than the schedule's.
  let lenAll := mode == 73
  -- The twin that finds the next window reaches it through a byte array. Mode 66 keeps the older
  -- route, a mask built and subtracted per divisor, so the two can still be timed against each
  -- other; the kernel checks the same literal either way. Measured on a quiet 32 vCPU box, three
  -- rounds alternating: the mask route spent 29.3 s of a 111.8 s window finding next windows, the
  -- byte array 4.2 s of 86.3 s, with the kernel unmoved, which is why the byte array is the
  -- default and the mask route is kept only for comparison.
  -- Mode 82 is mode 28 with one more sorted band: the octave where a divisor's eightfold fits the
  -- window and its sixteenfold does not, at sixteen records a divisor. Behind its own mode rather
  -- than inside 28, because 28 is what `run_segment` emits and the pair has not been measured at
  -- the full divisor set yet. Its case files must also import `PrimeCertTest.LaneChain`, which is
  -- where `stripeStepBand16` lives.
  let lane16 := mode == 82
  let maskTwin := mode == 66
  let stripes := mode == 28 || fold || sortOnly || tree || twoPass || marked || midLong || maskTwin
    || lenAll || lane16 || mode == 83 || mode == 84 || mode == 85
    || maskProbe || maskMulProbe || twoWinProbe || twoWinShiftProbe
  let sched := mode == 20 || mode == 21 || stripes
  -- Mode 84 is mode 28 with `batchLenLow`: the bottom tier at 1024 in place of 256, nothing else.
  -- It is the last of the schedule's four tiers to be varied on its own.
  let lowLong := mode == 84
  -- Mode 85 keeps the four lengths and moves the boundaries onto the band edges, so that each band
  -- is given one length. The values have been varied a tier at a time; the boundaries never have.
  let bandTier := mode == 85
  -- Mode 83 is mode 28 with `batchLenWide`, which differs from `batchLen` in one tier: 1536 over
  -- the wide band in place of 3072. Mode 21 already selects that schedule but without the sorted
  -- route, so it cannot say what the batch length alone is worth over the band that now holds the
  -- largest share of a window's kernel. This can.
  -- `wideTail` also turns on `tree` below, so a mode that only wants `batchLenWide` must not use
  -- it. Mode 83 did, and so measured the tree route rather than a batch length; it has its own
  -- flag now.
  let wideTail := mode == 21
  let wideShort := mode == 83
  let clamped := mode % 4 == 1 || mode % 4 == 3 || sched
  let slice := mode % 4 == 2 || mode % 4 == 3 || sched
  let tree := (mode % 8 ≥ 4 && !sched) || wideTail
  let fastTwin := mode ≥ 8
  let lo := index a
  let wm1 := W - 1
  let rounds := Nat.log2 wm1 + 1
  let step0 := Nat.max 1 len
  let sE := mkConst baseLit
  let loE := mkRawNatLit lo
  let wE := mkRawNatLit wm1
  let nE := mkRawNatLit rounds
  let initE := mkApp (mkConst ``initSegK) (mkRawNatLit W)
  let loopE (segE : Expr) (start n : Nat) : Expr :=
    if clamped then
      mkAppN (mkConst ``segLoopCK) #[sE, loE, wE, nE, segE, mkRawNatLit start, mkRawNatLit n]
    else mkSegLoopK sE loE wE segE start n
  let lhsLoop := loopE initE 1 fuel
  -- `run_segment` emits through this function too, and the names it has always emitted carry no
  -- mode and no `V`, so that a consumer of the sieve cannot tell which route built the window.
  let tag := if prodNames then s!"{a}_{W}_{fuel}_{step0}"
    else s!"{a}_{W}_{fuel}_{step0}_m{mode}"
  let parent := ns ++ Name.mkSimple (if prodNames then s!"segEq_{tag}" else s!"segEqV_{tag}")
  let litName := ns ++ Name.mkSimple (if prodNames then s!"segBits_{tag}" else s!"segBitsV_{tag}")
  if mode == 19 then
    -- Measurement only: the command's own computation, with one declaration emitted at the end,
    -- so its peak separates the loop's own footprint from the 2171 literals the other modes keep.
    let mut bitsL := initSeg W
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let owed := fuel - i * step0
      bitsL := segLoopC sVal lo wm1 rounds bitsL start (Nat.min step0 owed)
    addDecl <| Declaration.defnDecl
      { name := litName, levelParams := [], type := Nat.mkType,
        value := mkRawNatLit bitsL, hints := .regular 0, safety := .safe }
    return
  if mode == 51 || mode == 52 then
    -- Measurement only, over one of the two middle bands: mode 51 the divisors striking at most
    -- four times, mode 52 those striking at most eight. Each batch is settled by the sorted
    -- records the run uses today and by a tree with leaves of 262144 bits, alternating which goes
    -- first. `run.sh` reports the records under `batch lemmas` and the tree under `sorted batch
    -- lemmas`.
    let nrec := if mode == 51 then 4 else 8
    let mut first := 1
    while nrec * value first ≤ wm1 do
      first := first + 1
    let mut last := first
    while (nrec / 2) * value (last + 1) ≤ wm1 do
      last := last + 1
    let mut i := 0
    let mut start := first
    while start + step0 ≤ last do
      let stepN := step0
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let asm := treeAsmN sVal lo wm1 start stepN W nrec
      let (ls, cs, slotW, expect) := stripeSort sVal lo wm1 start stepN W nrec
      let emitRecords := do
        addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}"))
          (mkSegBeqTrue (mkAppN (mkConst ``stripeBatchK)
            #[mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN, mkRawNatLit W, wE,
              mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit (W / 65536)])
            (mkRawNatLit expect)) Lean.reflBoolTrue
      let emitTree := do
        addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"sstep_{i}"))
          (mkSegBeqTrue (mkAppN (mkConst (if mode == 51 then ``wtreeBatch4K else ``wtreeBatchK))
            #[mkRawNatLit cVal, loE, wE, mkRawNatLit start, mkRawNatLit stepN])
            (mkRawNatLit asm)) Lean.reflBoolTrue
      if i % 2 == 0 then
        emitRecords
        emitTree
      else
        emitTree
        emitRecords
      start := start + stepN
      i := i + 1
    return
  if mode == 25 || mode == 26 || mode == 27 || mode == 42 || mode == 43 || mode == 46
      || mode == 47 || mode == 48 || mode == 49 || mode == 50 then
    -- Measurement only, over the positions whose primes are past half the window's width, where a
    -- prime hits at most twice: mode 25 sorts each batch's hits into slices of the window, mode 26
    -- marks the same batches as the sieve does today, so the pair isolates that change. Mode 27 is
    -- mode 25 plus the clear a real run then owes, one `Nat.ldiff` of the window against the
    -- batch's assembled mask, which mode 25 leaves out and mode 26 carries inside its fold.
    let mut first := 1
    while 2 * value first ≤ wm1 do
      first := first + 1
    let count := fuel + 1 - first
    let mut bitsL := initSeg W
    for i in [0:(count + step0 - 1) / step0] do
      let start := first + i * step0
      let stepN := Nat.min step0 (count - i * step0)
      if mode == 26 then
        let next := segLoopC sVal lo wm1 rounds bitsL start stepN
        let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
        let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
        let batchE := mkAppN (mkConst ``segLoopSCK)
          #[mkRawNatLit cVal, loE, wE, nE, mkRawNatLit bitsL, mkRawNatLit start,
            mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsL := next
        continue
      if mode == 49 || mode == 50 then
        -- The same batch assembled through two leaf widths: 65536 bits against 262144 at mode 49,
        -- and 262144 against 1048576 at mode 50.
        let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
        let asm := treeAsm2 sVal lo wm1 start stepN W
        let args := #[mkRawNatLit cVal, loE, wE, mkRawNatLit start, mkRawNatLit stepN]
        let emitNarrow := do
          addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}"))
            (mkSegBeqTrue (mkAppN (mkConst
              (if mode == 50 then ``wtreeBatch2K else ``treeBatch2K)) args) (mkRawNatLit asm))
            Lean.reflBoolTrue
        let emitWide := do
          addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"sstep_{i}"))
            (mkSegBeqTrue (mkAppN (mkConst
              (if mode == 50 then ``vtreeBatch2K else ``wtreeBatch2K)) args) (mkRawNatLit asm))
            Lean.reflBoolTrue
        if i % 2 == 0 then
          emitNarrow
          emitWide
        else
          emitWide
          emitNarrow
        continue
      if mode == 48 then
        -- Four consecutive windows, struck by four walks of the batch and by one.
        let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
        let cE := mkRawNatLit cVal
        let sE' := mkRawNatLit start
        let lE := mkRawNatLit stepN
        let asms := (List.range 4).map fun j => treeAsm2 sVal (lo + j * W) wm1 start stepN W
        let emitFour := do
          for j in [0:4] do
            addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}_{j}"))
              (mkSegBeqTrue (mkAppN (mkConst ``treeBatch2K)
                #[cE, mkRawNatLit (lo + j * W), wE, sE', lE])
                (mkRawNatLit (asms[j]!))) Lean.reflBoolTrue
        let joined := (List.range 4).foldl (fun acc j => acc ||| (asms[j]! <<< (j * W))) 0
        let emitOne := do
          addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"sstep_{i}"))
            (mkSegBeqTrue (mkAppN (mkConst ``treeBatchQuad2K)
              #[cE, loE, wE, mkRawNatLit W, sE', lE]) (mkRawNatLit joined)) Lean.reflBoolTrue
        if i % 2 == 0 then
          emitFour
          emitOne
        else
          emitOne
          emitFour
        continue
      if mode == 47 then
        -- Two consecutive windows, struck by two walks of the batch and by one. `run.sh` reports
        -- `step_` and `sstep_` apart, so the two shapes land in separate columns.
        let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
        let asmA := treeAsm2 sVal lo wm1 start stepN W
        let asmB := treeAsm2 sVal (lo + W) wm1 start stepN W
        let cE := mkRawNatLit cVal
        let loBE := mkRawNatLit (lo + W)
        let sE' := mkRawNatLit start
        let lE := mkRawNatLit stepN
        let emitTwo := do
          addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}a"))
            (mkSegBeqTrue (mkAppN (mkConst ``treeBatch2K) #[cE, loE, wE, sE', lE])
              (mkRawNatLit asmA)) Lean.reflBoolTrue
          addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}b"))
            (mkSegBeqTrue (mkAppN (mkConst ``treeBatch2K) #[cE, loBE, wE, sE', lE])
              (mkRawNatLit asmB)) Lean.reflBoolTrue
        let emitOne := do
          addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"sstep_{i}"))
            (mkSegBeqTrue (mkAppN (mkConst ``treeBatchPair2K)
              #[cE, loE, wE, mkRawNatLit W, sE', lE])
              (mkRawNatLit (asmA ||| (asmB <<< W)))) Lean.reflBoolTrue
        if i % 2 == 0 then
          emitTwo
          emitOne
        else
          emitOne
          emitTwo
        continue
      if mode == 46 then
        -- The seed offset's two forms over the same batch, the old one first and the new one
        -- second, so that both arms meet the same runner and the same batches. `run.sh` reports
        -- `step_` and `sstep_` apart, so the two land in separate columns.
        let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
        let asm := treeAsm2 sVal lo wm1 start stepN W
        let args := #[mkRawNatLit cVal, loE, wE, mkRawNatLit start, mkRawNatLit stepN]
        let emitOld := do
          addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}"))
            (mkSegBeqTrue (mkAppN (mkConst ``treeBatch2OldK) args) (mkRawNatLit asm))
            Lean.reflBoolTrue
        let emitNew := do
          addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"sstep_{i}"))
            (mkSegBeqTrue (mkAppN (mkConst ``treeBatch2K) args) (mkRawNatLit asm))
            Lean.reflBoolTrue
        -- Which form goes first alternates by batch, so neither arm always pays whatever the
        -- first of a pair pays.
        if i % 2 == 0 then
          emitOld
          emitNew
        else
          emitNew
          emitOld
        continue
      if mode == 42 || mode == 43 then
        -- Mode 42 derives eight strikes a divisor and discards the six that pass the window's
        -- end; mode 43 derives the two this band actually has.
        let nrec := if mode == 43 then 2 else 8
        let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
        let asm := treeAsmN sVal lo wm1 start stepN W nrec
        let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
        let treeE := mkAppN (mkConst (if mode == 43 then ``treeBatch2K else ``treeBatchK))
          #[mkRawNatLit cVal, loE, wE, mkRawNatLit start, mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue treeE (mkRawNatLit asm)) Lean.reflBoolTrue
        bitsL := bitsL - (asm &&& bitsL)
        continue
      let (ls, cs, slotW, expect) := stripeSort sVal lo wm1 start stepN W 2
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let batchE := mkAppN (mkConst ``stripeBatchK)
        #[mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN, mkRawNatLit W, wE,
          mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit (W / 65536)]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit expect)) Lean.reflBoolTrue
      if mode == 27 then
        -- The two equations a run owes besides the batch itself: the record of which positions the
        -- batch accounted for, which is its own slice of the base sieve once per progression, and
        -- the clear, in the shape `clearHitK` and `ldiff_eq_sub` give it.
        let tallyName := mkPrivateName env (parent ++ Name.mkSimple s!"tally_{i}")
        let tallyE := mkApp2 (mkConst ``Nat.shiftRight) (mkRawNatLit expect) (mkRawNatLit W)
        let wantE := mkApp2 (mkConst ``Nat.lor) (mkRawNatLit cVal)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit cVal) (mkRawNatLit stepN))
        addSegThm tallyName (mkSegBeqTrue tallyE wantE) Lean.reflBoolTrue
        let next := bitsL - (expect &&& bitsL)
        let clearName := mkPrivateName env (parent ++ Name.mkSimple s!"clear_{i}")
        let clearE := mkApp2 (mkConst ``Nat.sub) (mkRawNatLit bitsL)
          (mkApp2 (mkConst ``Nat.land) (mkRawNatLit expect) (mkRawNatLit bitsL))
        addSegThm clearName (mkSegBeqTrue clearE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsL := next
    return
  if mode == 31 then
    -- Measurement only: the divisors whose double already passes the end of the segment, sorted
    -- with two records apiece under the two-bit record layout the other band needs. Against
    -- `Q9_Cleared`, which uses a one-bit layout, this says what one family of definitions for both
    -- bands would cost, the records themselves being the same two either way.
    let mut first := 1
    while 2 * value first ≤ wm1 do
      first := first + 1
    let count := fuel + 1 - first
    let mut bitsL := initSeg W
    for i in [0:(count + step0 - 1) / step0] do
      let start := first + i * step0
      let stepN := Nat.min step0 (count - i * step0)
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let (ls, cs, slotW, expect) := stripeSort sVal lo wm1 start stepN W 2
      let batchE := mkAppN (mkConst ``stripeBatchK)
        #[mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN, mkRawNatLit W, wE,
          mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit (W / 65536)]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit expect)) Lean.reflBoolTrue
      let tallyName := mkPrivateName env (parent ++ Name.mkSimple s!"tally_{i}")
      let tallyE := mkApp2 (mkConst ``Nat.shiftRight) (mkRawNatLit expect) (mkRawNatLit W)
      let mut wantV := 0
      for w in [0:2] do
        wantV := wantV ||| (cVal <<< (w * stepN))
      addSegThm tallyName (mkSegBeqTrue tallyE (mkRawNatLit wantV)) Lean.reflBoolTrue
      let next := bitsL - (expect &&& bitsL)
      let clearName := mkPrivateName env (parent ++ Name.mkSimple s!"clear_{i}")
      let clearE := mkApp2 (mkConst ``Nat.sub) (mkRawNatLit bitsL)
        (mkApp2 (mkConst ``Nat.land) (mkRawNatLit expect) (mkRawNatLit bitsL))
      addSegThm clearName (mkSegBeqTrue clearE (mkRawNatLit next)) Lean.reflBoolTrue
      bitsL := next
    return
  if mode == 86 then
    -- Mode 31's band and emitted shape at a **one-bit lane**, which is the whole of the experiment.
    --
    -- A record is sixteen bits. The three-bit format spends three naming which of eight strikes a
    -- record is and leaves thirteen for the position, so a batch holds 8192 divisors and no more.
    -- The wide band gives a divisor two strikes, so one bit names them, leaving fifteen: 32768.
    -- Mode 31 is the control and must be run at 8192 against this at 32768, one job, both peaks.
    --
    -- Timing only, no chain: the kernel still checks every literal emitted here, so the numbers are
    -- real, but nothing ties the batches back to the segment. That soundness argument is the band-2
    -- analogue of `stripeStep` and is only worth writing if this measures better.
    --
    -- This exists because the saving was costed by extrapolating two measured points past the range
    -- they were measured over, which decides nothing.
    if step0 > 32768 then
      throwError "run_segment_variant: mode 86 names one of two strikes in one bit and leaves \
        fifteen for the position, so a batch takes at most 32768 divisors, not {step0}"
    let mut first := 1
    while 2 * value first ≤ wm1 do
      first := first + 1
    let count := fuel + 1 - first
    let mut bitsL := initSeg W
    for i in [0:(count + step0 - 1) / step0] do
      let start := first + i * step0
      let stepN := Nat.min step0 (count - i * step0)
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let (ls, cs, slotW, expect) := SieveEmit.stripeSortOne sVal lo wm1 start stepN W
      let batchE := mkAppN (mkConst ``stripeBatchLK)
        #[mkRawNatLit 1, mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN,
          mkRawNatLit W, wE, mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs,
          mkRawNatLit (W / 65536)]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit expect)) Lean.reflBoolTrue
      let tallyName := mkPrivateName env (parent ++ Name.mkSimple s!"tally_{i}")
      let tallyE := mkApp2 (mkConst ``Nat.shiftRight) (mkRawNatLit expect) (mkRawNatLit W)
      let mut wantV := 0
      for w in [0:2] do
        wantV := wantV ||| (cVal <<< (w * stepN))
      addSegThm tallyName (mkSegBeqTrue tallyE (mkRawNatLit wantV)) Lean.reflBoolTrue
      let next := bitsL - (expect &&& bitsL)
      let clearName := mkPrivateName env (parent ++ Name.mkSimple s!"clear_{i}")
      let clearE := mkApp2 (mkConst ``Nat.sub) (mkRawNatLit bitsL)
        (mkApp2 (mkConst ``Nat.land) (mkRawNatLit expect) (mkRawNatLit bitsL))
      addSegThm clearName (mkSegBeqTrue clearE (mkRawNatLit next)) Lean.reflBoolTrue
      bitsL := next
    return
  if mode == 80 || mode == 81 then
    -- The octave below modes 78 and 79: a divisor whose sixteenfold fits the window and whose
    -- thirty-twofold does not, so thirty-two records name every strike. Mode 80 sorts them, mode
    -- 81 marks them the way the sieve does today. Sorting won the octave above by 13% of kernel
    -- and most of the peak, and the records double here while a mask does not, so this is where
    -- the two meet. Measurement only, no chain.
    if step0 > 2048 then
      throwError "run_segment_variant: mode {mode} packs a five-bit lane and an eleven-bit \
        position into a sixteen-bit record, so a batch takes at most 2048 divisors, not {step0}"
    let mut first := 1
    while 32 * value first ≤ wm1 do
      first := first + 1
    let mut last := first
    while 16 * value (last + 1) ≤ wm1 do
      last := last + 1
    let count := last + 1 - first
    let mut bitsX := initSeg W
    for i in [0:(count + step0 - 1) / step0] do
      let start := first + i * step0
      let stepN := Nat.min step0 (count - i * step0)
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      if mode == 81 then
        let next := segLoopC sVal lo wm1 rounds bitsX start stepN
        let batchE := mkAppN (mkConst ``segLoopSCK)
          #[mkRawNatLit cVal, loE, wE, nE, mkRawNatLit bitsX, mkRawNatLit start,
            mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsX := next
        continue
      let (ls, cs, slotW, expect) := SieveEmit.stripeSortX sVal lo wm1 start stepN W
      let batchE := mkAppN (mkConst ``stripeBatchXK)
        #[mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN, mkRawNatLit W, wE,
          mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit (W / 65536)]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit expect)) Lean.reflBoolTrue
      let tallyName := mkPrivateName env (parent ++ Name.mkSimple s!"tally_{i}")
      let tallyE := mkApp2 (mkConst ``Nat.shiftRight) (mkRawNatLit expect) (mkRawNatLit W)
      let mut wantV := 0
      for w in [0:32] do
        wantV := wantV ||| (cVal <<< (w * stepN))
      addSegThm tallyName (mkSegBeqTrue tallyE (mkRawNatLit wantV)) Lean.reflBoolTrue
    return
  if mode == 78 || mode == 79 then
    -- The octave below the one modes 34 and 35 cover: a divisor whose eightfold fits the window
    -- and whose sixteenfold does not, so sixteen records name every strike. Mode 78 sorts them,
    -- mode 79 marks them as the sieve does today, so the pair asks whether the sorted route is
    -- still ahead one octave further down. Measurement only, no chain.
    if step0 > 4096 then
      throwError "run_segment_variant: mode {mode} packs a four-bit lane and a twelve-bit \
        position into a sixteen-bit record, so a batch takes at most 4096 divisors, not {step0}"
    let mut first := 1
    while 16 * value first ≤ wm1 do
      first := first + 1
    let mut last := first
    while 8 * value (last + 1) ≤ wm1 do
      last := last + 1
    let count := last + 1 - first
    let mut bitsH := initSeg W
    for i in [0:(count + step0 - 1) / step0] do
      let start := first + i * step0
      let stepN := Nat.min step0 (count - i * step0)
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      if mode == 79 then
        let next := segLoopC sVal lo wm1 rounds bitsH start stepN
        let batchE := mkAppN (mkConst ``segLoopSCK)
          #[mkRawNatLit cVal, loE, wE, nE, mkRawNatLit bitsH, mkRawNatLit start,
            mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsH := next
        continue
      let (ls, cs, slotW, expect) := SieveEmit.stripeSortH sVal lo wm1 start stepN W
      let batchE := mkAppN (mkConst ``stripeBatchHK)
        #[mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN, mkRawNatLit W, wE,
          mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit (W / 65536)]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit expect)) Lean.reflBoolTrue
      let tallyName := mkPrivateName env (parent ++ Name.mkSimple s!"tally_{i}")
      let tallyE := mkApp2 (mkConst ``Nat.shiftRight) (mkRawNatLit expect) (mkRawNatLit W)
      -- Asking the tally for all sixteen lanes of every divisor is what stops one being skipped.
      let mut wantV := 0
      for w in [0:16] do
        wantV := wantV ||| (cVal <<< (w * stepN))
      addSegThm tallyName (mkSegBeqTrue tallyE (mkRawNatLit wantV)) Lean.reflBoolTrue
    return
  if mode == 34 || mode == 35 || mode == 37 || mode == 40 || mode == 41 || mode == 67
      || mode == 68 || mode == 71 || mode == 72 then
    -- Measurement only, over the band whose divisors have their quadruple inside the segment and
    -- their octuple past it, so each strikes at most four times per progression and eight records
    -- name every strike. Mode 34 sorts them, mode 35 marks them as the sieve does today. This is
    -- the octave below the band mode 29 covers, and it holds 47 percent of the divisors that the
    -- sorting leaves untouched today.
    -- Mode 37 sorts them exactly as mode 34 does but through `stripeBatchTK`, which reaches the
    -- same number with each shared subterm of a record written once, so the pair prices the
    -- repeated subterms on their own. Mode 67 is the same question asked again through
    -- `stripeBatchFK`, where the shared quantities are named by value rather than by `let`.
    let mut first := 1
    while 8 * value first ≤ wm1 do
      first := first + 1
    let mut last := first
    while 4 * value (last + 1) ≤ wm1 do
      last := last + 1
    let count := last + 1 - first
    let mut bitsL := initSeg W
    for i in [0:(count + step0 - 1) / step0] do
      let start := first + i * step0
      let stepN := Nat.min step0 (count - i * step0)
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      if mode == 35 then
        let next := segLoopC sVal lo wm1 rounds bitsL start stepN
        let batchE := mkAppN (mkConst ``segLoopSCK)
          #[mkRawNatLit cVal, loE, wE, nE, mkRawNatLit bitsL, mkRawNatLit start,
            mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsL := next
        continue
      if mode == 41 then
        -- The kernel finds the places itself, so the emitter owes it only the answer.
        let asm := treeAsmN sVal lo wm1 start stepN W 8
        let treeE := mkAppN (mkConst ``treeBatchK)
          #[mkRawNatLit cVal, loE, wE, mkRawNatLit start, mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue treeE (mkRawNatLit asm)) Lean.reflBoolTrue
        let next := bitsL - (asm &&& bitsL)
        let clearName := mkPrivateName env (parent ++ Name.mkSimple s!"clear_{i}")
        let clearE := mkApp2 (mkConst ``Nat.sub) (mkRawNatLit bitsL)
          (mkApp2 (mkConst ``Nat.land) (mkRawNatLit asm) (mkRawNatLit bitsL))
        addSegThm clearName (mkSegBeqTrue clearE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsL := next
        continue
      let (ls, cs, slotW, expect) := if mode == 40 then stripeSortS sVal lo wm1 start stepN W 8
        else if mode == 71 then SieveEmit.stripeSortW sVal lo wm1 start stepN W 8
        else if mode == 72 then SieveEmit.stripeSortG sVal lo wm1 start stepN W 8
        else stripeSort sVal lo wm1 start stepN W 8
      -- The join of mode 68 is by depth, so the window's slice count has to be a power of two.
      let npJ := W / 65536
      let dJ := Nat.log2 npJ
      if mode == 68 && (1 <<< dJ) != npJ then
        throwError "run_segment_variant: mode 68 joins by depth, so W / 65536 = {npJ} must be a \
          power of two"
      let batchE := if mode == 68 then
          mkAppN (mkConst ``stripeBatchJK)
            #[mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN, mkRawNatLit W, wE,
              mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit npJ, mkRawNatLit dJ]
        else
          mkAppN (mkConst (if mode == 37 then ``stripeBatchTK
            else if mode == 67 then ``stripeBatchFK
            else if mode == 72 then ``stripeBatchGK
            else if mode == 40 then ``stripeBatchS else ``stripeBatchK))
          #[mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN, mkRawNatLit W, wE,
            mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs,
            mkRawNatLit (if mode == 40 then W / 131072 else W / 65536)]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit expect)) Lean.reflBoolTrue
      let tallyName := mkPrivateName env (parent ++ Name.mkSimple s!"tally_{i}")
      let tallyE := mkApp2 (mkConst ``Nat.shiftRight) (mkRawNatLit expect) (mkRawNatLit W)
      -- Every mode but 71 asks the tally for all eight lanes of every divisor, which is what
      -- stops one being skipped. Mode 71 drops the records whose strike is past the window, so it
      -- asks only for the lanes it kept; that is why it is a screen and not a candidate.
      -- Mode 72's tally is complete, as every other mode's is, but it is assembled by the records
      -- that remain rather than one per lane, so the emitter states what it built.
      let mut wantV := if mode == 71 || mode == 72 then expect >>> W else 0
      if mode != 71 && mode != 72 then
        for w in [0:8] do
          wantV := wantV ||| (cVal <<< (w * stepN))
      addSegThm tallyName (mkSegBeqTrue tallyE (mkRawNatLit wantV)) Lean.reflBoolTrue
      let next := bitsL - (expect &&& bitsL)
      let clearName := mkPrivateName env (parent ++ Name.mkSimple s!"clear_{i}")
      let clearE := mkApp2 (mkConst ``Nat.sub) (mkRawNatLit bitsL)
        (mkApp2 (mkConst ``Nat.land) (mkRawNatLit expect) (mkRawNatLit bitsL))
      addSegThm clearName (mkSegBeqTrue clearE (mkRawNatLit next)) Lean.reflBoolTrue
      bitsL := next
    return
  if mode == 32 || mode == 33 || mode == 36 then
    -- Measurement only, over the divisors small enough that four times one still fits inside the
    -- segment, so each strikes it many times and the sorted route does not apply. Mode 32 joins a
    -- batch's masks into one and clears the segment against that once; mode 33 marks the segment
    -- once per divisor as the sieve does today. Joining lost by 2.6 times when it was tried over
    -- every divisor, where it paid doubling rounds on the large ones that the marking skips
    -- outright; over these divisors there are no such rounds to pay, which is what this asks.
    let mut last := 1
    while 4 * value (last + 1) ≤ wm1 do
      last := last + 1
    let mut bitsL := initSeg W
    for i in [0:(last + step0) / step0] do
      let start := 1 + i * step0
      let stepN := Nat.min step0 (last + 1 - (1 + i * step0))
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      if mode == 33 || mode == 36 then
        -- Mode 36 hands each batch the number of doubling rounds its own smallest divisor needs,
        -- where mode 33 hands every batch the number the whole segment needs. The rounds beyond
        -- that are no-ops either way, so both arms compute the same literal, and the difference is
        -- what those no-op rounds cost.
        let nb := if mode == 36 then Nat.log2 (wm1 / (2 * value start)) + 1 else rounds
        let next := segLoopC sVal lo wm1 nb bitsL start stepN
        let batchE := mkAppN (mkConst ``segLoopSCK)
          #[mkRawNatLit cVal, loE, wE, mkRawNatLit nb, mkRawNatLit bitsL, mkRawNatLit start,
            mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsL := next
        continue
      let acc := segAccLoopC sVal lo wm1 rounds 0 start stepN
      let batchE := mkAppN (mkConst ``segAccLoopSK)
        #[mkRawNatLit cVal, loE, wE, nE, mkRawNatLit 0, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit acc)) Lean.reflBoolTrue
      let next := bitsL - (acc &&& bitsL)
      let clearName := mkPrivateName env (parent ++ Name.mkSimple s!"clear_{i}")
      let clearE := mkApp2 (mkConst ``Nat.sub) (mkRawNatLit bitsL)
        (mkApp2 (mkConst ``Nat.land) (mkRawNatLit acc) (mkRawNatLit bitsL))
      addSegThm clearName (mkSegBeqTrue clearE (mkRawNatLit next)) Lean.reflBoolTrue
      bitsL := next
    return
  if mode == 29 || mode == 30 || mode == 44 then
    -- Measurement only, over the band whose divisors have their double inside the segment and
    -- their quadruple past it, so each strikes at most twice per progression: mode 29 sorts those
    -- strikes into slices, four records to a divisor, and mode 30 marks the same batches as the
    -- sieve does today. Mode 29 carries the tally and the clear a run would owe. Mode 44 has the
    -- kernel walk the positions and dispatch four strikes a divisor into a tree instead.
    let mut first := 1
    while 4 * value first ≤ wm1 do
      first := first + 1
    let mut last := first
    while 2 * value (last + 1) ≤ wm1 do
      last := last + 1
    let count := last + 1 - first
    let mut bitsL := initSeg W
    for i in [0:(count + step0 - 1) / step0] do
      let start := first + i * step0
      let stepN := Nat.min step0 (count - i * step0)
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      if mode == 30 then
        let next := segLoopC sVal lo wm1 rounds bitsL start stepN
        let batchE := mkAppN (mkConst ``segLoopSCK)
          #[mkRawNatLit cVal, loE, wE, nE, mkRawNatLit bitsL, mkRawNatLit start,
            mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsL := next
        continue
      if mode == 44 then
        let asm := treeAsmN sVal lo wm1 start stepN W 4
        let treeE := mkAppN (mkConst ``treeBatch4K)
          #[mkRawNatLit cVal, loE, wE, mkRawNatLit start, mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue treeE (mkRawNatLit asm)) Lean.reflBoolTrue
        bitsL := bitsL - (asm &&& bitsL)
        continue
      let (ls, cs, slotW, expect) := stripeSort sVal lo wm1 start stepN W 4
      let batchE := mkAppN (mkConst ``stripeBatchK)
        #[mkRawNatLit cVal, loE, mkRawNatLit start, mkRawNatLit stepN, mkRawNatLit W, wE,
          mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit (W / 65536)]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit expect)) Lean.reflBoolTrue
      let tallyName := mkPrivateName env (parent ++ Name.mkSimple s!"tally_{i}")
      let tallyE := mkApp2 (mkConst ``Nat.shiftRight) (mkRawNatLit expect) (mkRawNatLit W)
      let mut wantV := 0
      for w in [0, 1, 2, 3] do
        wantV := wantV ||| (cVal <<< (w * stepN))
      addSegThm tallyName (mkSegBeqTrue tallyE (mkRawNatLit wantV)) Lean.reflBoolTrue
      let next := bitsL - (expect &&& bitsL)
      let clearName := mkPrivateName env (parent ++ Name.mkSimple s!"clear_{i}")
      let clearE := mkApp2 (mkConst ``Nat.sub) (mkRawNatLit bitsL)
        (mkApp2 (mkConst ``Nat.land) (mkRawNatLit expect) (mkRawNatLit bitsL))
      addSegThm clearName (mkSegBeqTrue clearE (mkRawNatLit next)) Lean.reflBoolTrue
      bitsL := next
    return
  if mode == 24 then
    -- Measurement only: the same walk over the same primes, writing each prime's hits into one
    -- 65536-bit slice of the window instead of a number as wide as the window. Against mode 18 it
    -- gives what the width-dependent work costs per prime.
    let mut accT := 0
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let stepN := Nat.min step0 (fuel - i * step0)
      let next := segLoopStripe sVal lo wm1 0 accT start stepN
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let batchE := mkAppN (mkConst ``segLoopStripeK)
        #[mkRawNatLit cVal, loE, wE, mkRawNatLit 0, mkRawNatLit accT, mkRawNatLit start,
          mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
      accT := next
    return
  if mode == 23 then
    -- Measurement only: batches over an all-zero slice, so every step of the fold finds no prime
    -- and the window is returned unchanged. `fuel` steps in batches of `len` give the cost of the
    -- steps that a real run spends on positions holding no prime.
    let initLit := mkRawNatLit (initSeg W)
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let stepN := Nat.min step0 (fuel - i * step0)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let batchE := mkAppN (mkConst ``segLoopSCK)
        #[mkRawNatLit 0, loE, wE, nE, initLit, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE initLit) Lean.reflBoolTrue
    return
  if mode == 77 then
    -- Mode 18 on a split window: one comb of stride p, built at half the width, placed into each
    -- half. The emitter checks that unsplitting gives what the masks give. Timing only, no chain.
    let hw := W / 2
    let mut bitsT := SieveEmit.splitWindow (initSeg W) W
    let mut plain := initSeg W
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let stepN := Nat.min step0 (fuel - i * step0)
      let next := SieveEmit.splitLoop sVal lo hw rounds bitsT start stepN
      plain := segLoopC sVal lo wm1 rounds plain start stepN
      if SieveEmit.joinWindow next W != plain then
        throwError "run_segment_variant: the split window differs from the plain one, batch {i}"
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}"))
        (mkSegBeqTrue (mkAppN (mkConst ``splitLoopK)
          #[mkRawNatLit cVal, loE, mkRawNatLit hw, mkRawNatLit (hw - 1), nE,
            mkRawNatLit bitsT, mkRawNatLit start, mkRawNatLit stepN]) (mkRawNatLit next))
        Lean.reflBoolTrue
      bitsT := next
    return
  if mode == 76 then
    -- Mode 18 with the window marked by keeping rather than removing: one `land` a divisor in
    -- place of a mask, an `and`, a compare and a subtraction. Timing only, no chain.
    let mut bitsT := initSeg W
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let stepN := Nat.min step0 (fuel - i * step0)
      let next := SieveEmit.segLoopKeep sVal lo wm1 rounds bitsT start stepN
      if next != segLoopC sVal lo wm1 rounds bitsT start stepN then
        throwError "run_segment_variant: keeping left a different window from removing, batch {i}"
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}"))
        (mkSegBeqTrue (mkAppN (mkConst ``segLoopKeepK)
          #[mkRawNatLit cVal, loE, wE, nE, mkRawNatLit bitsT, mkRawNatLit start,
            mkRawNatLit stepN]) (mkRawNatLit next)) Lean.reflBoolTrue
      bitsT := next
    return
  if mode == 75 then
    -- Prices one `Nat.gcd` per slice at the sizes a certificate of that shape would use: the
    -- product of a slice's survivors against the product of the base primes above 32768. Both
    -- numbers are the emitter's, the statement is `Nat.beq (Nat.gcd a b) 1 = true`, and `gcd` is
    -- already on the kernel's fast path, so this needs no new definitions. It proves nothing
    -- about the sieve; it exists so the idea has a number before it has a design.
    -- Timed in three, because the first part is work the sieve already does and the second is the
    -- same for every window of a run, so only the third is a per-window cost this design adds.
    -- Each value is forced inside its own bracket, by a branch that cannot be taken without it.
    -- A `let` is not evaluated where it is written, and neither is `acc := acc + x.land 1`, which
    -- only builds another thunk: both leave the timers bracketing a binding while the work
    -- happens later, under whichever timer first needs the value. Only control flow forces.
    let mut forceAcc : Nat := 0
    let t0 ← IO.monoNanosNow
    let bits := segLoopC sVal lo wm1 rounds (initSeg W) 1 fuel
    if bits.land 1 == 0 then forceAcc := forceAcc + 1
    let t1 ← IO.monoNanosNow
    let bigP := SieveEmit.primorialOver sVal 32768 (value fuel)
    if bigP.land 1 == 0 then forceAcc := forceAcc + 2
    let t2 ← IO.monoNanosNow
    logInfo m!"primorial bits {bigP.log2 + 1}"
    logInfo m!"gcd emitter: window {(t1 - t0) / 1000000} ms, primorial {(t2 - t1) / 1000000} ms \
      (the window is work the sieve does anyway, the primorial is once a run)"
    let mut prodNanos : Nat := 0
    for k in [0:W / 65536] do
      let t3 ← IO.monoNanosNow
      let prod := SieveEmit.sliceProduct bits lo k
      if prod.land 1 == 0 then forceAcc := forceAcc + 4
      let t4 ← IO.monoNanosNow
      prodNanos := prodNanos + (t4 - t3)
      if k == 0 then logInfo m!"slice product bits {prod.log2 + 1}"
      addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"gcd_{k}"))
        (mkSegBeqTrue (mkApp2 (mkConst ``Nat.gcd) (mkRawNatLit prod) (mkRawNatLit bigP))
          (mkRawNatLit 1)) Lean.reflBoolTrue
    logInfo m!"gcd emitter: slice products {prodNanos / 1000000} ms (this is the per-window cost \
      the design adds, forced {forceAcc})"
    return
  if mode == 74 then
    -- Mode 18 with 5, 7, 11 and 13 cleared by one mask built at their shared period, then the
    -- rest of the divisors marked as usual from base index 5. Timing only, no chain.
    let combo := SieveEmit.comboClear (initSeg W) lo wm1
    if combo != segLoopC sVal lo wm1 rounds (initSeg W) 1 4 then
      throwError "run_segment_variant: the shared-period mask cleared a different window from \
        the four separate masks"
    addSegThm (mkPrivateName env (parent ++ Name.mkSimple "combo"))
      (mkSegBeqTrue (mkAppN (mkConst ``comboClearK) #[initE, loE, wE]) (mkRawNatLit combo))
      Lean.reflBoolTrue
    let mut bitsT := combo
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 5 + i * step0
      let stepN := Nat.min step0 (fuel + 1 - start)
      if stepN == 0 then break
      let next := segLoopC sVal lo wm1 rounds bitsT start stepN
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      addSegThm stepName
        (mkSegBeqTrue (mkAppN (mkConst ``segLoopSCK)
          #[mkRawNatLit cVal, loE, wE, nE, mkRawNatLit bitsT, mkRawNatLit start,
            mkRawNatLit stepN]) (mkRawNatLit next)) Lean.reflBoolTrue
      bitsT := next
    return
  if mode == 17 || mode == 18 || mode == 22 || mode == 69 || mode == 70 then
    -- Timing only: the per-batch checks with no chain and no final theorem, mode 17 through
    -- `segLoopSNK`, mode 18 through `segLoopSCK` and mode 22 through `segLoopSRK`, so the three
    -- isolate the mask builder. Mode 69 is mode 18 with the mask built to the window's width
    -- rather than to the next power of two, so the pair prices the span the last round leaves.
    let mut bitsT := initSeg W
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let owed := fuel - i * step0
      let stepN := Nat.min step0 owed
      let next := if mode == 17 then segLoopN sVal lo wm1 rounds bitsT start stepN
        else if mode == 22 then segLoopR sVal lo wm1 bitsT start stepN
        else if mode == 69 || mode == 70 then
          SieveEmit.segLoopE sVal lo wm1 rounds bitsT start stepN
        else segLoopC sVal lo wm1 rounds bitsT start stepN
      -- The narrower mask is a different construction, so the window it clears is checked against
      -- the window the existing twin clears rather than assumed equal.
      if (mode == 69 || mode == 70)
          && next != segLoopC sVal lo wm1 rounds bitsT start stepN then
        throwError "run_segment_variant: the mask built to the window's width cleared a different \
          window from the mask built by doubling, at batch {i}"
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let cE := mkRawNatLit cVal
      let chunkName := mkPrivateName env (parent ++ Name.mkSimple s!"chunk_{i}")
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let sliceE := mkApp2 (mkConst ``Nat.land)
        (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit start))
        (mkApp2 (mkConst ``Nat.sub)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit stepN)) (mkRawNatLit 1))
      addSegThm chunkName (mkSegBeqTrue sliceE cE) Lean.reflBoolTrue
      if mode == 70 then
        -- The batch's masks joined, then the window cleared once rather than once a divisor.
        let acc := SieveEmit.segAccLoopE sVal lo wm1 rounds 0 start stepN
        let accE := mkAppN (mkConst ``segAccLoopEK)
          #[cE, loE, wE, nE, mkRawNatLit 0, mkRawNatLit start, mkRawNatLit stepN]
        addSegThm stepName (mkSegBeqTrue accE (mkRawNatLit acc)) Lean.reflBoolTrue
        let clearName := mkPrivateName env (parent ++ Name.mkSimple s!"clear_{i}")
        let clearE := mkApp2 (mkConst ``Nat.sub) (mkRawNatLit bitsT)
          (mkApp2 (mkConst ``Nat.land) (mkRawNatLit bitsT) (mkRawNatLit acc))
        addSegThm clearName (mkSegBeqTrue clearE (mkRawNatLit next)) Lean.reflBoolTrue
        bitsT := next
        continue
      let batchE := if mode == 22 then
          mkAppN (mkConst ``segLoopSRK)
            #[cE, loE, wE, mkRawNatLit bitsT, mkRawNatLit start, mkRawNatLit stepN]
        else if mode == 69 then
          mkAppN (mkConst ``segLoopEK)
            #[cE, loE, wE, nE, mkRawNatLit bitsT, mkRawNatLit start, mkRawNatLit stepN]
        else
          mkAppN (mkConst (if mode == 17 then ``segLoopSNK else ``segLoopSCK))
            #[cE, loE, wE, nE, mkRawNatLit bitsT, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
      bitsT := next
    return
  if mode == 16 then
    let mut acc := 0
    let mut accE := mkRawNatLit 0
    let mut covered := 0
    let mut proofA : Expr := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero])
      #[Nat.mkType, mkAppN (mkConst ``segAccLoopK)
        #[sE, loE, wE, nE, mkRawNatLit 0, mkRawNatLit 1, mkRawNatLit 0]]
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      let owed := fuel - i * step0
      let stepN := Nat.min step0 owed
      let next := segAccLoopC sVal lo wm1 rounds acc start stepN
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let cE := mkRawNatLit cVal
      let chunkName := mkPrivateName env (parent ++ Name.mkSimple s!"chunk_{i}")
      let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
      let sliceE := mkApp2 (mkConst ``Nat.land)
        (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit start))
        (mkApp2 (mkConst ``Nat.sub)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit stepN)) (mkRawNatLit 1))
      addSegThm chunkName (mkSegBeqTrue sliceE cE) Lean.reflBoolTrue
      let batchE := mkAppN (mkConst ``segAccLoopSK)
        #[cE, loE, wE, nE, accE, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
      let leafName := mkPrivateName env (parent ++ Name.mkSimple s!"leaf_{i}")
      addSegThm leafName
        (mkNatEq (mkAppN (mkConst ``segAccLoopK)
          #[sE, loE, wE, nE, accE, mkRawNatLit start, mkRawNatLit stepN]) (mkRawNatLit next))
        (mkAppN (mkConst ``segAccLoopSK_leaf)
          #[sE, loE, wE, nE, accE, mkRawNatLit next, cE, mkRawNatLit start, mkRawNatLit stepN,
            mkConst chunkName, mkConst stepName])
      proofA := mkAppN (mkConst ``segAccLoopK_join)
        #[sE, loE, wE, nE, mkRawNatLit 0, accE, mkRawNatLit next, mkRawNatLit 1,
          mkRawNatLit covered, mkRawNatLit stepN, proofA, mkConst leafName]
      covered := covered + stepN
      acc := next
      accE := mkRawNatLit next
    let init := initSeg W
    let bits := init - (acc &&& init)
    addDecl <| Declaration.defnDecl
      { name := litName, levelParams := [], type := Nat.mkType,
        value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
    let accName := ns ++ Name.mkSimple s!"segAccV_{tag}"
    addSegThm accName
      (mkNatEq (mkAppN (mkConst ``segAccLoopK)
        #[sE, loE, wE, nE, mkRawNatLit 0, mkRawNatLit 1, mkRawNatLit fuel]) accE) proofA
    let clampedEq := mkAppN (mkConst ``segLoopCK_of_acc)
      #[sE, loE, wE, mkRawNatLit W, nE, accE, mkConst litName, mkRawNatLit fuel,
        mkConst accName, Lean.reflBoolTrue]
    addSegThm parent (mkNatEq (mkSegLoopK sE loE wE initE 1 fuel) (mkConst litName))
      (mkAppN (mkConst ``segEq_of_clamped)
        #[sE, loE, mkRawNatLit W, wE, nE, mkRawNatLit fuel, mkConst litName,
          Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, clampedEq])
    let bValA := value fuel
    addSegThm (ns ++ Name.mkSimple s!"segEqI_{tag}")
      (mkNatEq (mkAppN (mkConst ``segRun)
          #[sE, mkRawNatLit a, mkRawNatLit W, mkRawNatLit bValA]) (mkConst litName))
      (mkAppN (mkConst ``segRun_of)
        #[sE, mkRawNatLit a, loE, mkRawNatLit W, wE, mkRawNatLit bValA, mkRawNatLit fuel,
          mkConst litName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
          mkConst parent])
    return
  let mut bits := initSeg W
  let mut bitsE := initE
  let mut proof := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[Nat.mkType, lhsLoop]
  let mut nodes : Array (Name × Nat × Nat × Nat × Nat) := #[]
  let mut i := 0
  let mut start := 1
  if stripes then
    -- The sorted run chains through the unclamped loop rather than the clamped one, so that each
    -- batch can be handed the number of doubling rounds its own divisors need rather than the
    -- number the widest mask needs. `segLoopK_batch` is what drops the round count from the
    -- statement a batch contributes to the chain.
    let lhsK := mkSegLoopK sE loE wE initE 1 fuel
    proof := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[Nat.mkType, lhsK]
    -- The sorted shape costs more to elaborate than the shape it replaces, and subtracting two
    -- runs did not split that between the sorting and the records. This times the sorting itself,
    -- which answers it without a subtraction.
    let mut sortNanos : Nat := 0
    -- The marking pass an unsorted batch runs to find the window after it, which the clock above
    -- used to include, and a bit of each result read so that nothing is left unevaluated.
    let mut twinNanos : Nat := 0
    let mut forceAcc : Nat := 0
    while start ≤ fuel do
      let owed := fuel + 1 - start
      -- Mode 73 takes the batch length from the call for every batch, where the others take it
      -- from `batchLen`'s schedule below 700000 and from the call only above it. The schedule's
      -- 256, 512 and 768 were set long ago; a uniform length lets them be priced against one.
      -- Every schedule variant is chosen here, because this is the loop the banded run uses. The
      -- other site, in the branch below, is only reached by a mode that is not `stripes`; putting
      -- a flag there and expecting a banded run to see it leaves the mode inert, which is what
      -- happened to 84 and 85 first time and shows up as an unchanged batch lemma count.
      -- Note mode 28 takes the call's `len` above 700000, not `batchLen`'s 3072, so a variant that
      -- means to change one tier must leave that fall-through alone.
      let stepN := Nat.min
        (if lenAll then step0
          else if start < 700000 then
            (if midLong then batchLenMid start
              else if lowLong then batchLenLow start
              else if bandTier then batchLenBand wm1 start
              else batchLen start)
          else if wideShort then 1536
          else step0) owed
      let nb := Nat.min 32 (Nat.log2 (wm1 / value start) + 1)
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let cE := mkRawNatLit cVal
      let sorted := !marked && (wm1 < 2 * value start
        || (2 * value (start + stepN) ≤ wm1 && wm1 < 4 * value start)
        || (4 * value (start + stepN) ≤ wm1 && wm1 < 8 * value start)
        || (lane16 && 8 * value (start + stepN) ≤ wm1 && wm1 < 16 * value start))
      let chunkName := mkPrivateName env (parent ++ Name.mkSimple s!"chunk_{i}")
      let sliceE := mkApp2 (mkConst ``Nat.land)
        (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit start))
        (mkApp2 (mkConst ``Nat.sub)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit stepN)) (mkRawNatLit 1))
      addSegThm chunkName (mkSegBeqTrue sliceE cE) Lean.reflBoolTrue
      let batchE := mkAppN (mkConst ``segLoopSCK)
        #[cE, loE, wE, mkRawNatLit nb, bitsE, mkRawNatLit start, mkRawNatLit stepN]
      -- How many records a divisor of this batch needs, or none if the batch is not sorted.
      let nrec := if marked then 0
        else if wm1 < 2 * value start then 2
        else if 2 * value (start + stepN) ≤ wm1 && wm1 < 4 * value start then 4
        else if 4 * value (start + stepN) ≤ wm1 && wm1 < 8 * value start then 8
        else if lane16 && 8 * value (start + stepN) ≤ wm1 && wm1 < 16 * value start then 16
        else 0
      -- A sixteen-bit record holds a four-bit lane and a twelve-bit position, so a sixteen-record
      -- batch takes at most 4096 divisors. The graded schedule gives 256 to 768 over this band, so
      -- this never fires in practice; it is here so that it cannot fail silently if it ever would.
      if nrec == 16 && stepN > 4096 then
        throwError "run_segment_variant: a sixteen-record batch holds at most 4096 divisors, \
          not {stepN}"
      if nrec == 16 && !((← getEnv).contains (`PrimeCert.Sieve ++ Name.mkSimple
          "stripeStepBand16")) then
        throwError "run_segment_variant: mode {mode} closes its sixteen-record batches with \
          PrimeCert.Sieve.stripeStepBand16, which this file does not import. Add \
          `public meta import PrimeCertTest.LaneChain`."
      -- The widest band gets its own prefix in both modes, so that `run.sh` reports the band the
      -- tree replaces apart from the two it leaves alone and a pair can be read band by band.
      let batchName := mkPrivateName env (parent ++ Name.mkSimple
        (if nrec == 2 then s!"wstep_{i}" else if sorted then s!"sstep_{i}" else s!"step_{i}"))
      let treeHere := tree && (nrec == 2 || (allTree && nrec > 0))
      let t0 ← IO.monoNanosNow
      let sortRes := if nrec == 0 || treeHere then none
        else if nrec == 16 then some (SieveEmit.stripeSortH sVal lo wm1 start stepN W)
        else some (stripeSort sVal lo wm1 start stepN W nrec)
      let asmRes := if treeHere then some (treeAsmN sVal lo wm1 start stepN W nrec) else none
      -- Looking at the answer is what forces the work, so each clock below covers what precedes
      -- it. Reading one bit of a result is enough to force it and costs nothing beside the window.
      forceAcc := forceAcc + (match asmRes with | some asm => asm.land 1 | none => 0)
      if let some (_, _, _, expect) := sortRes then
        if expect == 0 then throwError "run_segment_variant: the sorted batch came out empty"
      let t1 ← IO.monoNanosNow
      sortNanos := sortNanos + (t1 - t0)
      -- The window after this batch is the window with the batch's mask cleared from it, so a
      -- batch that has already assembled its mask needs no second marking pass to find it. Only
      -- an unsorted batch, which assembles nothing, still runs the twin. That pass used to sit
      -- inside the clock above, where it was reported as part of the sort; it is timed apart now.
      let twin := fun _ : Unit =>
        if maskTwin then segLoopC sVal lo wm1 nb bits start stepN
        else segLoopCBytes sVal lo wm1 bits start stepN
      let next := if twoPass then twin () else
        match sortRes, asmRes with
        | some (_, _, _, expect), _ => bits - (expect &&& bits)
        | _, some asm => bits - (asm &&& bits)
        | _, _ => twin ()
      forceAcc := forceAcc + next.land 1
      let t2 ← IO.monoNanosNow
      twinNanos := twinNanos + (t2 - t1)
      let batchProof :=
        if sortOnly then Lean.reflBoolTrue
        else if treeHere then
          let asm := asmRes.getD 0
          let args := #[cE, loE, wE, mkRawNatLit nb, mkRawNatLit W, mkRawNatLit start,
            mkRawNatLit stepN, bitsE, mkRawNatLit asm, mkRawNatLit next]
          if nrec == 2 then
            mkAppN (mkConst (if wideLeaf then ``wtreeStep2
              else if derivedStrike then ``treeStep2E else ``treeStep2))
              (args ++ Array.replicate 6 Lean.reflBoolTrue)
          else
            mkAppN (mkConst (if nrec == 4 then ``wtreeStep4 else ``wtreeStep8))
              (args ++ Array.replicate 8 Lean.reflBoolTrue)
        else match sortRes with
        | none => Lean.reflBoolTrue
        | some (ls, cs, slotW, expect) =>
          let args := #[cE, loE, wE, mkRawNatLit nb, mkRawNatLit W, mkRawNatLit start,
            mkRawNatLit stepN, mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs,
            mkRawNatLit (W / 65536), bitsE, mkRawNatLit expect, mkRawNatLit next]
          let refls := Array.replicate (if nrec == 2 then 8 else 10) Lean.reflBoolTrue
          -- `stripeStepBand16` is in `PrimeCertTest.LaneChain`, which imports this module, so it
          -- is not in scope here; it is in scope wherever a case file imports both. Naming it by
          -- `Name.mkSimple` rather than `` ` `` is what lets that work, and the check above says
          -- so plainly if a case file forgot the import.
          let band16 := `PrimeCert.Sieve ++ Name.mkSimple "stripeStepBand16"
          mkAppN (mkConst (if nrec == 2 then ``stripeStep
            else if nrec == 4 then ``stripeStepBand
            else if nrec == 16 then band16 else ``stripeStepBand8)) (args ++ refls)
      let batchRef ← if fold then pure batchProof else do
        addSegThm batchName (mkSegBeqTrue batchE (mkRawNatLit next)) batchProof
        pure (mkConst batchName)
      -- Mode 59 adds, to each batch of the widest band, one equation that walks the batch's
      -- positions and counts the divisors without placing a strike. Its statements are mode 45's
      -- plus that one, so the pair prices the walk apart from the strikes.
      if walkProbe && nrec == 2 then
        let walkName := mkPrivateName env (parent ++ Name.mkSimple s!"wwalk_{i}")
        let cnt := (setBitsLow (sVal >>> start) stepN).size
        addSegThm walkName
          (mkSegBeqTrue (mkAppN (mkConst ``walkCountK) #[cE, mkRawNatLit stepN])
            (mkRawNatLit cnt)) Lean.reflBoolTrue
      if (twoWinProbe || twoWinShiftProbe) && nrec == 0 then
        let mut acc := 0
        for j in setBitsLow (sVal >>> start) stepN do
          let p := value (start + j)
          let d := p * 2
          let m1 := buildMaskC p wm1 (firstLoc (index (p * 5)) lo d)
            (firstLoc (index (p * 7)) lo d) nb
          let m2 := buildMaskC p wm1 (firstLoc (index (p * 5)) (lo + W) d)
            (firstLoc (index (p * 7)) (lo + W) d) nb
          acc := acc ||| ((m1 ||| m2) &&& ((1 <<< W) - 1))
        let twoName := mkPrivateName env (parent ++ Name.mkSimple s!"stwo_{i}")
        addSegThm twoName
          (mkSegBeqTrue (mkAppN (mkConst (if twoWinShiftProbe then ``orMask2SK else ``orMask2CK))
            #[cE, loE, wE, mkRawNatLit nb, mkRawNatLit start, mkRawNatLit stepN,
              mkRawNatLit W]) (mkRawNatLit acc)) Lean.reflBoolTrue
      if (maskProbe || maskMulProbe) && nrec == 0 then
        let mut acc := 0
        for j in setBitsLow (sVal >>> start) stepN do
          let p := value (start + j)
          let d := p * 2
          acc := acc ||| buildMaskC p wm1 (firstLoc (index (p * 5)) lo d)
            (firstLoc (index (p * 7)) lo d) nb
        let maskName := mkPrivateName env (parent ++ Name.mkSimple s!"smask_{i}")
        addSegThm maskName
          (mkSegBeqTrue (mkAppN (mkConst (if maskMulProbe then ``orMaskMK else ``orMaskCK))
            #[cE, loE, wE, mkRawNatLit nb, mkRawNatLit start, mkRawNatLit stepN])
            (mkRawNatLit acc)) Lean.reflBoolTrue
      if bucketProbe && nrec == 2 then
        -- The strikes of the batch in leaf order, which is the order the sort already puts the
        -- records in, packed one to a 32-bit field.
        let mut strikes : Array Nat := #[]
        for j in setBitsLow (sVal >>> start) stepN do
          let p := value (start + j)
          let d := p * 2
          for X in [firstLoc (index (p * 5)) lo d, firstLoc (index (p * 7)) lo d] do
            if X ≤ wm1 then
              strikes := strikes.push X
        let sorted := strikes.qsort (· < ·)
        -- One equation a chunk: the kernel reports deep recursion on a fold over a whole batch's
        -- strikes, and a chunk keeps the leaves of a run grouped all the same.
        let chunk := 512
        for base in [0:(sorted.size + chunk - 1) / chunk] do
          let hi := Nat.min sorted.size ((base + 1) * chunk)
          let mut q := 0
          let mut want := 0
          for j in [base * chunk:hi] do
            q := q ||| (sorted[j]! <<< (32 * (j - base * chunk)))
            want := want ||| (1 <<< sorted[j]!)
          let joinName := mkPrivateName env (parent ++ Name.mkSimple s!"wjoin_{i}_{base}")
          addSegThm joinName
            (mkSegBeqTrue (mkAppN (mkConst ``bucketJoinK)
              #[mkRawNatLit q, mkRawNatLit (hi - base * chunk)]) (mkRawNatLit want))
            Lean.reflBoolTrue
      if seedProbe && nrec == 2 then
        let seedName := mkPrivateName env (parent ++ Name.mkSimple s!"wseed_{i}")
        let mut tot := 0
        for j in setBitsLow (sVal >>> start) stepN do
          let p := value (start + j)
          let d := p * 2
          tot := tot + firstLoc (index (p * 5)) lo d + firstLoc (index (p * 7)) lo d
        addSegThm seedName
          (mkSegBeqTrue (mkAppN (mkConst ``seedSumK)
            #[cE, loE, mkRawNatLit start, mkRawNatLit stepN]) (mkRawNatLit tot))
          Lean.reflBoolTrue
      let stepName := mkPrivateName env (parent ++ Name.mkSimple
        (if fold && sorted then s!"sstep_{i}" else s!"plain_{i}"))
      addSegThm stepName
        (mkSegBeqTrue (mkSegLoopK sE loE wE bitsE start stepN) (mkRawNatLit next))
        (mkAppN (mkConst ``segLoopK_batch)
          #[sE, cE, loE, wE, mkRawNatLit nb, mkRawNatLit W, bitsE, mkRawNatLit start,
            mkRawNatLit stepN, mkRawNatLit next, Lean.reflBoolTrue, Lean.reflBoolTrue,
            Lean.reflBoolTrue, Lean.reflBoolTrue, mkConst chunkName, batchRef])
      proof := if owed == stepN then
          mkAppN (mkConst ``segLoopK_last)
            #[lhsK, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
              proof, mkConst stepName]
        else
          mkAppN (mkConst ``segLoopK_chain)
            #[lhsK, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
              mkRawNatLit (owed - stepN), proof, mkConst stepName]
      bits := next
      bitsE := mkRawNatLit next
      start := start + stepN
      i := i + 1
    logInfo m!"stripeSort total {sortNanos / 1000000} ms"
    logInfo m!"segLoopC total {twinNanos / 1000000} ms (forced {forceAcc})"
    addDecl <| Declaration.defnDecl
      { name := litName, levelParams := [], type := Nat.mkType,
        value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
    addSegThm parent (mkNatEq lhsK (mkConst litName)) proof
    let bValS := value fuel
    addSegThm (ns ++ Name.mkSimple s!"segEqI_{tag}")
      (mkNatEq (mkAppN (mkConst ``segRun)
          #[sE, mkRawNatLit a, mkRawNatLit W, mkRawNatLit bValS]) (mkConst litName))
      (mkAppN (mkConst ``segRun_of)
        #[sE, mkRawNatLit a, loE, mkRawNatLit W, wE, mkRawNatLit bValS, mkRawNatLit fuel,
          mkConst litName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
          mkConst parent])
    return
  while start ≤ fuel do
    let owed := fuel + 1 - start
    let stepN := Nat.min
      (if lowLong then batchLenLow start
        else if bandTier then batchLenBand wm1 start
        else if wideTail then batchLenWide start
        else if sched then batchLen start else step0) owed
    let next := if fastTwin then segLoopC sVal lo wm1 rounds bits start stepN
      else segLoop sVal lo wm1 bits start stepN
    -- A batch settled by sorting is named `sstep_` rather than `step_`, so that a timing run can
    -- report the two kinds apart.
    let sorted := stripes && (wm1 < 2 * value start
      || (2 * value (start + stepN) ≤ wm1 && wm1 < 4 * value start))
    let stepName := mkPrivateName env (parent ++ Name.mkSimple
      (if sorted then s!"sstep_{i}" else s!"step_{i}"))
    let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
    let cE := mkRawNatLit cVal
    let chunkName := mkPrivateName env (parent ++ Name.mkSimple s!"chunk_{i}")
    if slice then
      let sliceE := mkApp2 (mkConst ``Nat.land)
        (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit start))
        (mkApp2 (mkConst ``Nat.sub)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit stepN)) (mkRawNatLit 1))
      addSegThm chunkName (mkSegBeqTrue sliceE cE) Lean.reflBoolTrue
      let batchE := if clamped then
          mkAppN (mkConst ``segLoopSCK)
            #[cE, loE, wE, nE, bitsE, mkRawNatLit start, mkRawNatLit stepN]
        else
          mkAppN (mkConst ``segLoopSK) #[cE, loE, wE, bitsE, mkRawNatLit start, mkRawNatLit stepN]
      if stripes && wm1 < 2 * value start then
        -- Every divisor of this batch has its double past the end of the segment, so each strikes
        -- at most twice, and the batch is settled by sorting those strikes into slices of the
        -- segment. `stripeStep` names the eight tests the kernel then owes.
        let (ls, cs, slotW, expect) := stripeSort sVal lo wm1 start stepN W 2
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next))
          (mkAppN (mkConst ``stripeStep)
            #[cE, loE, wE, nE, mkRawNatLit W, mkRawNatLit start, mkRawNatLit stepN,
              mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit (W / 65536), bitsE,
              mkRawNatLit expect, mkRawNatLit next, Lean.reflBoolTrue, Lean.reflBoolTrue,
              Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
              Lean.reflBoolTrue, Lean.reflBoolTrue])
      else if stripes && 2 * value (start + stepN) ≤ wm1 && wm1 < 4 * value start then
        -- Every divisor of this batch has its double inside the segment and its quadruple past the
        -- end, so each strikes at most four times and gets four records.
        let (ls, cs, slotW, expect) := stripeSort sVal lo wm1 start stepN W 4
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next))
          (mkAppN (mkConst ``stripeStepBand)
            #[cE, loE, wE, nE, mkRawNatLit W, mkRawNatLit start, mkRawNatLit stepN,
              mkRawNatLit slotW, mkRawNatLit ls, mkRawNatLit cs, mkRawNatLit (W / 65536), bitsE,
              mkRawNatLit expect, mkRawNatLit next, Lean.reflBoolTrue, Lean.reflBoolTrue,
              Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
              Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue])
      else
        addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
    else
      addSegThm stepName (mkSegBeqTrue (loopE bitsE start stepN) (mkRawNatLit next))
        Lean.reflBoolTrue
    if tree then
      let leafName := mkPrivateName env (parent ++ Name.mkSimple s!"leaf_{i}")
      let leafProof := match clamped, slice with
        | false, false => mkAppN (mkConst ``segLoopK_of_beq)
            #[sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
              mkConst stepName]
        | true, false => mkAppN (mkConst ``segLoopCK_of_beq)
            #[sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
              mkConst stepName]
        | false, true => mkAppN (mkConst ``segLoopSK_leaf)
            #[sE, loE, wE, bitsE, mkRawNatLit next, cE, mkRawNatLit start, mkRawNatLit stepN,
              mkConst chunkName, mkConst stepName]
        | true, true => mkAppN (mkConst ``segLoopSCK_leaf)
            #[sE, loE, wE, nE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, mkConst chunkName, mkConst stepName]
      addSegThm leafName (mkNatEq (loopE bitsE start stepN) (mkRawNatLit next)) leafProof
      nodes := nodes.push (leafName, start, stepN, bits, next)
    else
      proof := match clamped, slice, owed == stepN with
        | false, false, true => mkAppN (mkConst ``segLoopK_last)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst stepName]
        | false, false, false => mkAppN (mkConst ``segLoopK_chain)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst stepName]
        | true, false, true => mkAppN (mkConst ``segLoopCK_last)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst stepName]
        | true, false, false => mkAppN (mkConst ``segLoopCK_chain)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst stepName]
        | false, true, true => mkAppN (mkConst ``segLoopSK_last)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst chunkName, mkConst stepName]
        | false, true, false => mkAppN (mkConst ``segLoopSK_chain)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst chunkName,
              mkConst stepName]
        | true, true, true => mkAppN (mkConst ``segLoopSCK_last)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst chunkName, mkConst stepName]
        | true, true, false => mkAppN (mkConst ``segLoopSCK_chain)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst chunkName,
              mkConst stepName]
    bits := next
    bitsE := mkRawNatLit next
    start := start + stepN
    i := i + 1
  if tree then
    let mut level := 0
    while nodes.size > 1 do
      let mut next : Array (Name × Nat × Nat × Nat × Nat) := #[]
      for j in [0:(nodes.size + 1) / 2] do
        if 2 * j + 1 < nodes.size then
          let (n1, s1, l1, b1, m1) := nodes[2 * j]!
          let (n2, _, l2, _, b2) := nodes[2 * j + 1]!
          let joinName := mkPrivateName env (parent ++ Name.mkSimple s!"join_{level}_{j}")
          let joinProof := if clamped then
              mkAppN (mkConst ``segLoopCK_join)
                #[sE, loE, wE, nE, mkRawNatLit b1, mkRawNatLit m1, mkRawNatLit b2,
                  mkRawNatLit s1, mkRawNatLit l1, mkRawNatLit l2, mkConst n1, mkConst n2]
            else
              mkAppN (mkConst ``segLoopK_join)
                #[sE, loE, wE, mkRawNatLit b1, mkRawNatLit m1, mkRawNatLit b2,
                  mkRawNatLit s1, mkRawNatLit l1, mkRawNatLit l2, mkConst n1, mkConst n2]
          addSegThm joinName
            (mkNatEq (loopE (mkRawNatLit b1) s1 (l1 + l2)) (mkRawNatLit b2)) joinProof
          next := next.push (joinName, s1, l1 + l2, b1, b2)
        else
          next := next.push nodes[2 * j]!
      nodes := next
      level := level + 1
    let some (topName, _, _, _, _) := nodes[0]?
      | throwError "run_segment_variant: the join tree is empty"
    proof := mkConst topName
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := Nat.mkType,
      value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
  let finalProof := if clamped then
      mkAppN (mkConst ``segEq_of_clamped)
        #[sE, loE, mkRawNatLit W, wE, nE, mkRawNatLit fuel, mkRawNatLit bits,
          Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue, proof]
    else proof
  addSegThm parent (mkNatEq (mkSegLoopK sE loE wE initE 1 fuel) (mkConst litName)) finalProof
  let bVal := value fuel
  addSegThm (ns ++ Name.mkSimple s!"segEqI_{tag}")
    (mkNatEq (mkAppN (mkConst ``segRun)
        #[sE, mkRawNatLit a, mkRawNatLit W, mkRawNatLit bVal]) (mkConst litName))
    (mkAppN (mkConst ``segRun_of)
      #[sE, mkRawNatLit a, loE, mkRawNatLit W, wE, mkRawNatLit bVal, mkRawNatLit fuel,
        mkConst litName, Lean.reflBoolTrue, Lean.reflBoolTrue, Lean.reflBoolTrue,
        mkConst parent])

/-- `run_segment a W fuel len` sieves the window of `W` wheel positions from `a` by the base
primes at wheel indices `1 … fuel`. A trailing numeral names another base sieve by its bound, as
`run_segment a W fuel len 100000000`; the default base is the `1000000` sieve from
`PrimeCert.SieveBase`. The emitted names carry all four numerals, so distinct calls never collide.

It sieves by bands: a divisor striking the window only once or twice has its strikes sorted into
the slice each lands in, and only a divisor striking often enough to be worth one is given a mask.
`len` is the batch length above base index 700000; below it the graded schedule of `batchLen`
applies, which was settled on windows per machine-hour rather than seconds per window.

The sorted route writes each strike into one 65536-bit slice of the window, so it needs a window
that is a whole number of slices. A narrower window, or one that is not a multiple of 65536, goes
through the single clamped loop instead, which sieves the same window to the same literal and ends
at the same two theorems. The ladder of small windows at the end of this file takes that path.

Measured against the single clamped loop this command used before, both arms in one job on a fresh
c7i.8xlarge at W = 4194304 over 333333 divisors: kernel **65.5-65.9 s against 85.5-86.3**,
processor **73.2-73.6 against 128.5-130.0**, peak 1.72 GB against 1.90. The old loop is
`run_segment_variant 0` unclamped and `9` clamped. -/
elab "run_segment" aStx:num wStx:num fStx:num lStx:num bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    let W := wStx.getNat
    if W % 65536 == 0 then
      runSegmentV (← getCurrNamespace) base 28 aStx.getNat W fStx.getNat lStx.getNat
        (prodNames := true)
    else
      runSegment (← getCurrNamespace) base aStx.getNat W fStx.getNat lStx.getNat

/-! ## Marking only the divisors that strike something

Counted on the window at `100000000000001`, W = 4194304 (`scripts/gcd_skippable_by_band.py`):
**497131 of 661067 base divisors above 32768 strike nothing still live, and build a mask that
clears not one bit.** By band the fraction climbs with the number of strikes a divisor has, from
0.329 over the masked small band to **0.905 over the wide band**, which is the largest single
kernel cost in a window.

`segLoopK_eq_self_of_blocks` is what would let those be skipped soundly. It takes the divisor set
as a bitmask rather than a range, which matters: the skippable divisors are **scattered**, mean run
5.51 and longest 237, so the range form `segLoopK_eq_self_of_range` reaches only 4072 of them and
is no use here. Against a bitmask the whole skipped set is covered by one gcd per slice, 64 in all.

`live` here means the window after marking by the divisors up to `thr`, a prefix of the loop. That
choice is what makes the test well founded rather than circular, and marking only ever clears bits,
so a divisor that strikes nothing live at that point still strikes nothing once the rest of the
marking has happened.

**This emits no chain and proves no soundness**, so it measures rather than certifies: the gcd
equations and every batch literal are kernel-checked, and what is missing is the step from them to
`segLoopK s … = segLoopK sMark …`. The emitter does check its own skip set, by rebuilding the
window from the marked subset alone and refusing to emit if it differs from the full one.

`parts` also switches off the self-check, which is a **second full marking pass** that production
would never run, and which otherwise counts toward the time and the peak of every timing arm.
Adding 3 keeps the same emission and drops the check: 3 both, 4 gcds alone, 5 route alone. The
small cases are where the skip set is shown to be right, and the kernel still checks every literal
emitted, so an arm run without the check is a timing rather than a claim.

`parts` splits the two halves so a measurement can say which of them costs what, the full window at
a 65536-bit slice having reached 40 GB against the control's 2.61 with the kernel barely started.
0 emits both, 1 the gcd equations alone, 2 the marking route over the marked subset alone. **2 is
the upper bound on what the idea can buy**: it marks only the divisors that strike and certifies
nothing, so no certificate can do better than it, and if it saves nothing against mode 28 then no
certificate is worth looking for. Neither 1 nor 2 is sound on its own. -/
/-- Append a line to `/tmp/skip-rss.log` and flush it.

Twice now this has had to move further out. `logInfo` holds its messages until the command
finishes, so a command the watchdog kills prints none of them. Writing to `IO.getStderr` does not
help either: the command elaborator runs inside `IO.FS.withIsolatedStreams`, so that handle is the
captured stream rather than the real file descriptor, and the capture is turned into messages at
the same point `logInfo` would have been. **A file opened by name is outside both**, which is the
whole reason for the path here. Read it after the kill; it is not in the `out-` or `time-` file. -/
meta def rssLog (msg : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/skip-rss.log" IO.FS.Mode.append
  h.putStrLn s!"skip rss: {msg}"
  h.flush

/-- Empty `/tmp/skip-rss.log`, so a run's lines are its own rather than the previous run's with
this one appended. Called once at the start of the emitter. -/
meta def rssLogInit : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/skip-rss.log" IO.FS.Mode.write
  h.flush

/-- Resident memory of this process in MiB, from the second field of `/proc/self/statm`, which
counts pages. Returns 0 where that file is not readable, so a platform without it reports zeros
rather than failing a build. -/
meta def rssMB : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/statm"
    match (s.splitOn " ")[1]? with
    | some p => return ((p.trimAscii.toNat?.getD 0) * 4) / 1024
    | none => return 0
  catch _ => return 0

public meta def runSegmentSkip (ns baseLit : Name) (a W fuel len thr bs parts : Nat) :
    MetaM Unit := do
  let env ← getEnv
  let some info := env.find? baseLit
    | throwError "run_segment_skip: no base sieve {baseLit}"
  let some sVal := info.value?.bind Expr.rawNatLit?
    | throwError "run_segment_skip: the base sieve {baseLit} is not a numeral"
  if bs == 0 || W % bs ≠ 0 then
    throwError "run_segment_skip: the certificate states one gcd per slice of {bs} bits, so the \
      slice must divide the window {W}"
  let lo := index a
  let wm1 := W - 1
  let rounds := Nat.log2 wm1 + 1
  -- The divisors up to `thr` are marked unconditionally; they define what `live` means.
  let mut tIdx := 1
  while value (tIdx + 1) ≤ thr do
    tIdx := tIdx + 1
  let step0 := Nat.max 1 len
  -- 0 both and check, 1 gcds and check, 2 route and check, 3 both, 4 gcds, 5 route, 6 neither,
  -- 7 neither but check. 6 computes the skip set and emits nothing, which is the sharp question
  -- after `ZZP` ran away with the gcds already switched off: it leaves only the marking pass.
  let emitGcd := parts == 0 || parts == 1 || parts == 3 || parts == 4
  let emitRoute := parts == 0 || parts == 2 || parts == 3 || parts == 5
  let doCheck := parts ≤ 2 || parts == 7
  let t0 ← IO.monoMsNow
  -- One marking pass, recording which divisors cleared a bit. `segMarkC` forms that comparison
  -- anyway, so the striking set costs the pass itself and no separate probe.
  --
  -- Taken in batches of `len`, the way mode 19 takes it and the banded route takes its own, rather
  -- than over every divisor in one call. `ZZP_SkipRouteOnly` reached 40 GB and was killed before
  -- printing a line, with the gcds not emitted at all, which puts it here rather than in the
  -- certificate.
  let nBatch := (fuel + step0 - 1) / step0
  rssLogInit
  rssLog s!"entry {← rssMB} MiB, {nBatch} batches of {step0}, W {W}, fuel {fuel}, parts {parts}"
  let mut full := initSeg W
  let mut hits := 0
  let mut nHit := 0
  let mut nTot := 0
  for i in [0:nBatch] do
    let start := 1 + i * step0
    let stepN := Nat.min step0 (fuel - i * step0)
    let (b, h, nh, nt) := SieveEmit.segLoopHits sVal lo wm1 rounds full start stepN
    full := b
    hits := hits ||| h
    nHit := nHit + nh
    nTot := nTot + nt
    -- Logged inside the loop, because every run so far has died before reaching any line after
    -- it, which tells us only that it got no further than here.
    if i % 32 == 0 || i + 1 == nBatch then
      rssLog s!"marking batch {i} of {nBatch}, {← rssMB} MiB"
  let t1 ← IO.monoMsNow
  -- `thr` keeps the divisors up to it marked whether or not they strike. Taking live in the order
  -- the loop runs makes that unnecessary, so `thr = 0` is the setting to use and anything larger
  -- only grows the marked set.
  let keep := sVal &&& ((1 <<< (tIdx + 1)) - 1)
  let sMark := if thr == 0 then hits else hits ||| keep
  let sSkip := Nat.ldiff (sVal &&& ((1 <<< (fuel + 1)) - 1)) sMark
  -- Counted off the masks themselves rather than from `nHit`, which would double count whatever
  -- `thr` keeps that also struck.
  let nMark := (SieveEmit.setBitsLow (sMark >>> 1) fuel).size
  let nSkip := (SieveEmit.setBitsLow (sSkip >>> 1) fuel).size
  let t2 ← IO.monoMsNow
  rssLog s!"after split {← rssMB} MiB"
  -- The emitter's own check that the skip set is right: the marked subset alone must build the
  -- same window as every divisor does. A wrong skip test fails here rather than in a timing.
  let mut final := full
  if doCheck then
    final := initSeg W
    for i in [0:(fuel + step0 - 1) / step0] do
      let start := 1 + i * step0
      final := segLoopC sMark lo wm1 rounds final start (Nat.min step0 (fuel - i * step0))
  if final != full then
    throwError "run_segment_skip: the marked subset builds a different window from the full \
      divisor set, so the skip test is wrong"
  let t3 ← IO.monoMsNow
  rssLog s!"after check {← rssMB} MiB"
  rssLog s!"marking pass {t1 - t0} ms | split {t2 - t1} ms | check {t3 - t2} ms"
  rssLog s!"marked {nMark} | skipped {nSkip} of {nTot} | struck {nHit} | thr {thr}"
  let markName := ns ++ Name.mkSimple s!"skipMark_{a}_{W}_{fuel}"
  let skipName := ns ++ Name.mkSimple s!"skipSet_{a}_{W}_{fuel}"
  rssLog s!"before the two subset literals {← rssMB} MiB"
  for (nm, v) in [(markName, sMark), (skipName, sSkip)] do
    addDecl <| Declaration.defnDecl
      { name := nm, levelParams := [], type := Nat.mkType,
        value := mkRawNatLit v, hints := .regular 0, safety := .safe }
  -- One gcd a slice, against the product of the skipped divisors, in the shape
  -- `segLoopK_eq_self_of_blocks` takes its hypotheses.
  let pE := mkAppN (mkConst ``prodLiveFromK)
    #[mkConst skipName, mkRawNatLit 0, mkRawNatLit 1, mkRawNatLit fuel]
  let segE := mkRawNatLit final
  let nGcd := if emitGcd then W / bs else 0
  rssLog s!"{nGcd} gcds over slices of {bs} bits, parts {parts}, \
    route {if emitRoute then "on" else "off"}, check {if doCheck then "on" else "off"}"
  for k in [0:nGcd] do
    let liveE := mkAppN (mkConst ``prodLiveFromK)
      #[segE, mkRawNatLit lo, mkRawNatLit (k * bs), mkRawNatLit bs]
    addSegThm (mkPrivateName env (ns ++ Name.mkSimple s!"skipGcd_{k}"))
      (mkSegBeqTrue (mkApp2 (mkConst ``Nat.gcd) liveE pE) (mkRawNatLit 1))
      Lean.reflBoolTrue
  -- The marking route itself, unchanged, over the marked subset in place of the base sieve.
  rssLog s!"after the gcds, before the route {← rssMB} MiB"
  if emitRoute then
    runSegmentV ns markName 28 a W fuel len
  rssLog s!"done {← rssMB} MiB"

/-- `run_segment_variant mode a W fuel len` is `run_segment a W fuel len` run through the loop and
the twin chosen by `mode`, 0 to 15 (see `runSegmentV`), with the same optional trailing base-sieve
bound. -/
elab "run_segment_variant" mStx:num aStx:num wStx:num fStx:num lStx:num bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    runSegmentV (← getCurrNamespace) base mStx.getNat aStx.getNat wStx.getNat fStx.getNat
      lStx.getNat

/-- `run_segment_skip a W fuel len thr bs` emits the window the way `run_segment` does, but marks
only the divisors that strike something still live, and states one `Nat.gcd` per slice of `bs` bits
over the ones it skipped. `thr` sets what live means: the divisors up to it are marked
unconditionally, and is flat anywhere from 16384 to 262144. Measurement only, no chain.

`bs` is open because the kernel refused the statement at 65536 with "deep recursion detected", on a
four-slice window, having taken the same slice size on a one-slice window. `prodLiveFromK` is a
`Nat.rec` over the slice, so the slice size is what sets how deep that term goes. -/
elab "run_segment_skip" aStx:num wStx:num fStx:num lStx:num tStx:num sStx:num
    bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    runSegmentSkip (← getCurrNamespace) base aStx.getNat wStx.getNat fStx.getNat lStx.getNat
      tStx.getNat sStx.getNat 0

/-- `run_segment_skip_part parts a W fuel len thr bs` is `run_segment_skip` emitting one half of
what it emits: `parts` 1 for the gcd equations alone, 2 for the marking route alone, 0 for both.
Its own command rather than a seventh argument to `run_segment_skip`, so that the argument cannot
be read as the trailing base-sieve bound in a case that predates it. -/
elab "run_segment_skip_part" pStx:num aStx:num wStx:num fStx:num lStx:num tStx:num sStx:num
    bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    runSegmentSkip (← getCurrNamespace) base aStx.getNat wStx.getNat fStx.getNat lStx.getNat
      tStx.getNat sStx.getNat pStx.getNat

/-- Emit the batch equations of one window on a chosen wheel, and nothing else: no chain, no
`segRun`, no soundness. `wheel` is 6 or 30. The two differ only in how many integers a bit stands
for, so a pair of calls at the same width and the same divisors prices the wheels against each
other, and the kernel checks every literal in both. -/
public meta def runWheel (ns baseLit : Name) (wheel a W fuel len : Nat) : MetaM Unit := do
  if wheel ≠ 6 && wheel ≠ 30 then throwError "run_wheel: the wheel {wheel} is not 6 or 30"
  if W = 0 then throwError "run_wheel: the window is empty"
  let env ← getEnv
  let some info := env.find? baseLit | throwError "run_wheel: no base sieve {baseLit}"
  let some sVal := info.value?.bind Expr.rawNatLit?
    | throwError "run_wheel: the base sieve {baseLit} is not a numeral"
  let lo := if wheel == 6 then index a else SieveEmit.index30 a
  let wm1 := W - 1
  let step0 := Nat.max 1 len
  let sE := mkConst baseLit
  let loE := mkRawNatLit lo
  let wE := mkRawNatLit wm1
  let nb := Nat.min 32 (Nat.log2 (wm1 / value 1) + 1)
  let nbE := mkRawNatLit nb
  let loopC := mkConst (if wheel == 6 then ``segLoopCK else ``segLoop30CK)
  let tag := s!"{wheel}_{a}_{W}_{fuel}_{step0}"
  let parent := ns ++ Name.mkSimple s!"wheelEq_{tag}"
  -- 5 divides 30, so a window of that wheel holds no multiple of it and it is not one of its
  -- divisors; `index30K (5 * m)` would read a rank entry that stands for nothing. The wheel of
  -- six starts at 5 as usual. One divisor in tens of thousands separates the two scans.
  let first := if wheel == 6 then 1 else 2
  let mut bits := initSeg W
  for i in [0:(fuel + step0 - 1) / step0] do
    let start := first + i * step0
    let stepN := Nat.min step0 (fuel - i * step0)
    let next := if wheel == 6 then segLoopC sVal lo wm1 nb bits start stepN
      else SieveEmit.segLoop30C sVal lo wm1 nb bits start stepN
    let lhs := mkAppN loopC
      #[sE, loE, wE, nbE, mkRawNatLit bits, mkRawNatLit start, mkRawNatLit stepN]
    addSegThm (mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}"))
      (mkSegBeqTrue lhs (mkRawNatLit next)) Lean.reflBoolTrue
    bits := next

/-- `run_wheel wheel a W fuel len` emits one window's batch equations on the wheel of `wheel`
(6 or 30), for timing one wheel against the other. It proves nothing about the window. -/
elab "run_wheel" kStx:num aStx:num wStx:num fStx:num lStx:num bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    runWheel (← getCurrNamespace) base kStx.getNat aStx.getNat wStx.getNat fStx.getNat
      lStx.getNat

/-! ## Worked instances

A ladder of windows well above the base range, built smallest first. The arguments are
`a W fuel len`: the window of `W` wheel positions from `a`, sieved by the base primes at wheel
indices `1 … fuel` (the numbers up to `value fuel`), in `len`-step batches.

The last line is the widest that has been through the kernel here: 1024 wheel positions from
`10^16 + 1`, sieved by every prime up to `10^6`. Wider or deeper cases belong in
`PrimeCertTest/SegBench`, which is not part of `defaultTargets`. -/

run_segment 1000000000001 16 100 16
run_segment 1000000000001 64 100 16
run_segment 100000000000001 16 100 16
run_segment 10000000000000001 16 100 16
run_segment 10000000000000001 256 1000 16
run_segment 10000000000000001 1024 3333 16
run_segment 10000000000000001 4096 3333 16
run_segment 10000000000000001 1024 33333 16
run_segment 10000000000000001 256 333333 512
run_segment 1000000000000000001 64 100 16
run_segment_variant 16 1000000000001 64 100 16
run_segment 10000000000000001 1024 333333 512

end PrimeCert.Sieve
