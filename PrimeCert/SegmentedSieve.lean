/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Lean.Elab.Command
public import PrimeCert.Sieve
public import PrimeCert.SieveCorrect
public import PrimeCert.SieveBase

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
`segLoopK s lo Wm1 (initSegK W) 1 fuel = <literal>`; the bridge from that to primality,
`SegmentSound`, is stated but not proved. See the module note at `SegmentSound`.
-/

namespace PrimeCert.Sieve

open Nat

/-! ## Kernel-side definitions -/

/-- A window of `W` live candidates: the low `W` bits set, i.e. `2^W - 1`. -/
@[expose] public def initSegK (W : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 W) 1

/-- The least offset `j` with `lo + j` in the residue class of `A` modulo `m`. -/
@[expose] public def firstLocK (A lo m : Nat) : Nat :=
  Nat.mod (Nat.sub (Nat.add A (Nat.mul m (Nat.succ (Nat.div lo m)))) lo) m

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

/-- `segMarkK` with seeds dropped outside the window, `n` doubling rounds, no rounds at all when
`2 * p > Wm1` (only the seeds can then land in the window), and no subtraction when nothing hits. -/
@[expose] public noncomputable def segMarkCK (seg p lo Wm1 n : Nat) : Nat :=
  ((p.mul 2).ble Wm1).rec
    (clearHitK seg (seg.land
      ((seedK (firstLocK (indexK (p.mul 5)) lo (p.mul 2)) Wm1).lor
        (seedK (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) Wm1))))
    (clearHitK seg (seg.land
      (buildMaskCK p Wm1 (firstLocK (indexK (p.mul 5)) lo (p.mul 2))
        (firstLocK (indexK (p.mul 7)) lo (p.mul 2)) n)))

/-- `segLoopK` marking with `segMarkCK`. -/
@[expose] public noncomputable def segLoopCK (s lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK s (start.add i)).rec b (segMarkCK b (valueK (start.add i)) lo Wm1 n)

/-- `segLoopK` reading the base primes from a slice `c` of the base sieve: bit `i` of `c` stands for
base index `start + i`. -/
@[expose] public noncomputable def segLoopSK (c lo Wm1 seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkK b (valueK (start.add i)) lo Wm1)

/-- `segLoopSK` marking with `segMarkCK`. -/
@[expose] public noncomputable def segLoopSCK (c lo Wm1 n seg start fuel : Nat) : Nat :=
  fuel.rec seg fun i b =>
    (testBitK c i).rec b (segMarkCK b (valueK (start.add i)) lo Wm1 n)

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

/-! ## What the window holds

The two facts below are the arithmetic that segmentation actually adds: the local seed is the
right one, and a local offset names the number you expect. -/

/-- `firstLocK` in ordinary notation, for use in proofs. -/
public theorem firstLocK_eq {A lo m : ℕ} :
    firstLocK A lo m = (A + m * (lo / m + 1) - lo) % m := rfl

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
    congr 1
    lia
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

/-- The intended correctness statement for a segment: every surviving bit of the window names a
number with no prime factor among the base primes. **Not proved here.** The pieces it needs
(`testBit_buildMaskK`, `prog_iff_dvd`, `mask_iff`, `testBit_markMaskK`) are file-local in
`PrimeCert.SieveCorrect`, so proving this means either re-deriving them or exporting them. -/
public def SegmentSound (s B a W : ℕ) : Prop :=
  ∀ j < W, (segLoopK s (index a) (W - 1) (initSegK W) 1 (index B)).testBit j →
    ∀ q ≤ B, q.Prime → ¬ q ∣ value (index a + j)

/-! ## Compiled twins

Executable copies of the definitions above, used by `run_segment` to compute the batch literals.
The kernel checks each batch equation, so a twin that disagreed would make `run_segment` fail. -/

meta def initSeg (W : Nat) : Nat := (1 <<< W) - 1

meta def firstLoc (A lo m : Nat) : Nat := (A + m * (lo / m + 1) - lo) % m

meta def segMark (seg p lo Wm1 : Nat) : Nat :=
  seg - (seg &&& buildMask p Wm1 (firstLoc (index (p * 5)) lo (p * 2))
    (firstLoc (index (p * 7)) lo (p * 2)) 32)

meta def segLoop (s lo Wm1 seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in [0:fuel] do
    let j := start + i
    if s &&& (1 <<< j) ≠ 0 then
      b := segMark b (value j) lo Wm1
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

/-- Add a theorem declaration with the given statement and proof term. -/
meta def addSegThm (name : Name) (type value : Expr) : MetaM Unit :=
  addDecl <| Declaration.thmDecl { name, levelParams := [], type, value }

/-- Sieve the window of `W` wheel positions starting at the number `a` by the base primes held in
the bitset `baseLit`, scanning `fuel` base indices in batches of `len`. Emits
`ns.segBits_{a}_{W}_{fuel}_{len} : Nat` and `ns.segEq_{a}_{W}_{fuel}_{len} : segLoopK … =
segBits_…`, the latter chained from one kernel-checked `Nat.beq` lemma per batch. `ns` is the
namespace the call sits in, so the same window can be built in two modules without a clash. -/
meta def runSegment (ns baseLit : Name) (a W fuel len : Nat) : MetaM Unit := do
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
  let initE := mkApp (mkConst ``initSegK) (mkRawNatLit W)
  let lhsLoop := mkSegLoopK sE loE wE initE 1 fuel
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
    let next := segLoop sVal lo wm1 bits start stepN
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
    addSegThm stepName
      (mkSegBeqTrue (mkSegLoopK sE loE wE bitsE start stepN) (mkRawNatLit next)) Lean.reflBoolTrue
    proof := if owed == stepN then
        mkAppN (mkConst ``segLoopK_last)
          #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
            proof, mkConst stepName]
      else
        mkAppN (mkConst ``segLoopK_chain)
          #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start, mkRawNatLit stepN,
            mkRawNatLit (owed - stepN), proof, mkConst stepName]
    bits := next
    bitsE := mkRawNatLit next
  addDecl <| Declaration.defnDecl
    { name := litName, levelParams := [], type := Nat.mkType,
      value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
  addSegThm parent (mkNatEq lhsLoop (mkConst litName)) proof

/-- `run_segment a W fuel len` sieves the window of `W` wheel positions from `a` by the base
primes at wheel indices `1 … fuel`, in batches of `len` steps. A trailing numeral names another
base sieve by its bound, as `run_segment a W fuel len 100000000`; the default base is the
`1000000` sieve from `PrimeCert.SieveBase`. The emitted names carry all four numerals, so
distinct calls never collide. -/
elab "run_segment" aStx:num wStx:num fStx:num lStx:num bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    runSegment (← getCurrNamespace) base aStx.getNat wStx.getNat fStx.getNat lStx.getNat

/-- `runSegment` with a choice of loop, for timing the draft variants against each other. `mode`
0 is `segLoopK`, 1 is `segLoopCK`, 2 is `segLoopSK` and 3 is `segLoopSCK`. Modes 2 and 3 emit one
lemma checking the slice of the base sieve (`…chunk_{i}`) per batch as well as the batch lemma
(`…step_{i}`). Modes 0, 1 and 2 chain their batches into `ns.segEqV_{tag}`, mode 2 through
`segLoopSK_chain`, which carries the slice equation. Mode 3 stops at the per-batch lemmas, since
the bridge from `segMarkCK` to `segMarkK` is not written. Every batch literal comes from the
`segLoop` twin, so every mode is checked against the same values. -/
meta def runSegmentV (ns baseLit : Name) (mode a W fuel len : Nat) : MetaM Unit := do
  if a % 6 ≠ 1 && a % 6 ≠ 5 then
    throwError "run_segment_variant: the window start {a} is not 1 or 5 modulo 6"
  if W = 0 then throwError "run_segment_variant: the window is empty"
  if mode > 3 then throwError "run_segment_variant: mode {mode} is not 0, 1, 2 or 3"
  let env ← getEnv
  let some info := env.find? baseLit
    | throwError "run_segment_variant: no base sieve {baseLit}"
  let some sVal := info.value?.bind Expr.rawNatLit?
    | throwError "run_segment_variant: the base sieve {baseLit} is not a numeral"
  let clamped := mode == 1 || mode == 3
  let slice := mode == 2 || mode == 3
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
  let tag := s!"{a}_{W}_{fuel}_{step0}_m{mode}"
  let parent := ns ++ Name.mkSimple s!"segEqV_{tag}"
  let litName := ns ++ Name.mkSimple s!"segBitsV_{tag}"
  let mut bits := initSeg W
  let mut bitsE := initE
  let mut proof := mkAppN (mkConst ``Eq.refl [Level.succ Level.zero]) #[Nat.mkType, lhsLoop]
  for i in [0:(fuel + step0 - 1) / step0] do
    let start := 1 + i * step0
    let owed := fuel - i * step0
    let stepN := Nat.min step0 owed
    let next := segLoop sVal lo wm1 bits start stepN
    let stepName := mkPrivateName env (parent ++ Name.mkSimple s!"step_{i}")
    if slice then
      let cVal := (sVal >>> start) &&& ((1 <<< stepN) - 1)
      let cE := mkRawNatLit cVal
      let sliceE := mkApp2 (mkConst ``Nat.land)
        (mkApp2 (mkConst ``Nat.shiftRight) sE (mkRawNatLit start))
        (mkApp2 (mkConst ``Nat.sub)
          (mkApp2 (mkConst ``Nat.shiftLeft) (mkRawNatLit 1) (mkRawNatLit stepN)) (mkRawNatLit 1))
      let chunkName := mkPrivateName env (parent ++ Name.mkSimple s!"chunk_{i}")
      addSegThm chunkName (mkSegBeqTrue sliceE cE) Lean.reflBoolTrue
      let batchE := if clamped then
          mkAppN (mkConst ``segLoopSCK)
            #[cE, loE, wE, nE, bitsE, mkRawNatLit start, mkRawNatLit stepN]
        else
          mkAppN (mkConst ``segLoopSK) #[cE, loE, wE, bitsE, mkRawNatLit start, mkRawNatLit stepN]
      addSegThm stepName (mkSegBeqTrue batchE (mkRawNatLit next)) Lean.reflBoolTrue
      unless clamped do
        proof := if owed == stepN then
            mkAppN (mkConst ``segLoopSK_last)
              #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
                mkRawNatLit stepN, proof, mkConst chunkName, mkConst stepName]
          else
            mkAppN (mkConst ``segLoopSK_chain)
              #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, cE, mkRawNatLit start,
                mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst chunkName,
                mkConst stepName]
    else
      addSegThm stepName (mkSegBeqTrue (loopE bitsE start stepN) (mkRawNatLit next))
        Lean.reflBoolTrue
      proof := match clamped, owed == stepN with
        | false, true => mkAppN (mkConst ``segLoopK_last)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst stepName]
        | false, false => mkAppN (mkConst ``segLoopK_chain)
            #[lhsLoop, sE, loE, wE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst stepName]
        | true, true => mkAppN (mkConst ``segLoopCK_last)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, proof, mkConst stepName]
        | true, false => mkAppN (mkConst ``segLoopCK_chain)
            #[lhsLoop, sE, loE, wE, nE, bitsE, mkRawNatLit next, mkRawNatLit start,
              mkRawNatLit stepN, mkRawNatLit (owed - stepN), proof, mkConst stepName]
    bits := next
    bitsE := mkRawNatLit next
  unless slice && clamped do
    addDecl <| Declaration.defnDecl
      { name := litName, levelParams := [], type := Nat.mkType,
        value := mkRawNatLit bits, hints := .regular 0, safety := .safe }
    addSegThm parent (mkNatEq lhsLoop (mkConst litName)) proof

/-- `run_segment_variant mode a W fuel len` is `run_segment a W fuel len` run through the loop
chosen by `mode` (see `runSegmentV`), with the same optional trailing base-sieve bound. -/
elab "run_segment_variant" mStx:num aStx:num wStx:num fStx:num lStx:num bStx:(num)? : command =>
  liftTermElabM <| do
    let base := match bStx with
      | none => ``sieveBits_1000000
      | some b => `PrimeCert.Sieve ++ Name.mkSimple s!"sieveBits_{b.getNat}"
    runSegmentV (← getCurrNamespace) base mStx.getNat aStx.getNat wStx.getNat fStx.getNat
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
run_segment 10000000000000001 1024 333333 512

end PrimeCert.Sieve
