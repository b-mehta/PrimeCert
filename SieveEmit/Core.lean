/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

/-! # The emitter's arithmetic, in a precompiled library

`run_segment_variant` works out each batch's literals before it states them, and that arithmetic is
ordinary `Nat` code rather than anything to do with proofs. A definition imported from a library
without `precompileModules` runs in the interpreter when an elaborator calls it, so this library
holds the arithmetic on its own and the lakefile precompiles it; `PrimeCert.SegmentedSieve` keeps
the proofs, the kernel definitions these are twins of, and the elaborator itself.

Nothing here is trusted. The kernel checks every literal these produce against the corresponding
kernel definition, so a function here that disagreed with its twin would make a run fail rather
than certify something false. -/

namespace SieveEmit

/-- The `k`th integer coprime to 6, matching `PrimeCert.Sieve.value`. -/
public def valueE (k : Nat) : Nat := (k * 3 + 1) + k % 2

/-- Where an integer coprime to 6 sits in that enumeration, matching `PrimeCert.Sieve.index`. -/
public def indexE (q : Nat) : Nat := (q - 1) / 3

public def initSeg (W : Nat) : Nat := (1 <<< W) - 1

public def firstLoc (A lo m : Nat) : Nat := (A + m - lo % m) % m

/-- Which of the low `len` bits of `c` are set, read a word at a time. Shifting a `len`-bit number
down by one copies the whole number, so a scan that steps one bit at a time rebuilds `c` once per
position; peeling 64 bits at a time leaves the bit tests inside a single word.

**Still quadratic in `len`, so pass a batch length and never the whole divisor range.** Each
`rest >>> 64` copies what is left of `rest`, so the cost grows with `len / 64` shifts of a
`len`-bit number. At `len = 8192`, a batch, that is 128 shifts of a kilobyte and does not signify.
At `len = 3333333`, the whole range, it is some 52000 shifts of a 416 KB number, tens of GB of
allocation; two such calls in the skip emitter's counting lines are what killed it at 40 GB.
Callers in this file all pass a batch length; keep it that way. -/
public def setBitsLow (c len : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut rest := c &&& ((1 <<< len) - 1)
  for w in [0:(len + 63) / 64] do
    let word := rest &&& 0xFFFFFFFFFFFFFFFF
    if word ≠ 0 then
      for b in [0:64] do
        if (word >>> b) &&& 1 = 1 then
          out := out.push (64 * w + b)
    rest := rest >>> 64
  return out

/-- Twin of `seedK`. -/
public def seedC (A M : Nat) : Nat := if A ≤ M then 1 <<< A else 0

/-- Twin of `buildMaskCK`. -/
public def buildMaskC (p M A B n : Nat) : Nat := Id.run do
  let mut m := seedC A M ||| seedC B M
  for i in [0:n] do
    let sh := p <<< (i + 1)
    if sh ≤ M then
      m := m ||| (m <<< sh)
  return m

/-- Twin of `segMarkCK`. -/
public def segMarkC (seg p lo Wm1 n : Nat) : Nat :=
  let A := firstLoc (indexE (p * 5)) lo (p * 2)
  let B := firstLoc (indexE (p * 7)) lo (p * 2)
  let mask := if p * 2 ≤ Wm1 then buildMaskC p Wm1 A B n else seedC A Wm1 ||| seedC B Wm1
  let hit := mask &&& seg
  if hit = 0 then seg else seg - hit

/-- Twin of `buildMaskNK`. -/
public def buildMaskN (p M A B n : Nat) : Nat := Id.run do
  let terms := M / (p * 2) + 1
  let seeds := (1 <<< A) ||| (1 <<< B)
  let mut m := 0
  for i in [0:n] do
    let c := terms >>> (n - i)
    m := m ||| (m <<< (p * 2 * c))
    if (terms >>> (n - i - 1)) &&& 1 = 1 then
      m := m ||| (seeds <<< (p * 2 * (c * 2)))
  return m

/-- Twin of `buildMaskRK`. -/
public def buildMaskR (p M A B : Nat) : Nat :=
  let m := p * 2
  ((2 ^ (m * (M / m + 1)) - 1) / (2 ^ m - 1)) * ((1 <<< A) ||| (1 <<< B))

/-- `stripeSort` for 131072-bit slices: a seed's slice is its top bits above 17, its place within
the slice the low 17, and a window of `W` positions holds `W / 131072` of them. -/
public def stripeSortS (s lo Wm1 start len W nrec : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 131072
  let mut slots : Array (Array Nat) := Array.replicate (np + 1) #[]
  let mut slotAsm : Array Nat := Array.replicate np 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:nrec] do
      let X := (if w &&& 1 = 0 then b5 else b7) + (w >>> 1) * d
      if X ≤ Wm1 then
        slots := slots.modify (X >>> 17) (·.push (8 * i + w))
        slotAsm := slotAsm.modify (X >>> 17) (· ||| (1 <<< (X &&& 131071)))
      else
        slots := slots.modify np (·.push (8 * i + w))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 131072))
  let mut seen := 0
  for w in [0:nrec] do
    seen := seen ||| (c <<< (w * len))
  let mut slotW := 16
  for k in [0:np + 1] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np + 1] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

/-- Sort a batch's divisors by the slice of the segment each of their strikes lands in. Returns the
packed lists, the packed counts, the widest slot in bits, and the value `stripeBatchK` should give.
A record's low two bits name one of a divisor's four possible strikes: the low bit picks the
progression and the next steps it on by a further double. `nrec` says how many records a divisor
gets, two where its double already passes the end of the segment and four where its double fits and
its quadruple does not. -/
public def stripeSort (s lo Wm1 start len W nrec : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 65536
  let mut slots : Array (Array Nat) := Array.replicate (np + 1) #[]
  -- The assembled mask is built one slice at a time rather than one bit at a time: joining a bit
  -- into a slice touches 65536 bits where joining it into the whole mask touches `W`.
  let mut slotAsm : Array Nat := Array.replicate np 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    -- Both progressions are found once a divisor, where the records of a divisor read them
    -- `nrec` times between them.
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:nrec] do
      let X := (if w &&& 1 = 0 then b5 else b7) + (w >>> 1) * d
      if X ≤ Wm1 then
        slots := slots.modify (X >>> 16) (·.push (8 * i + w))
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
      else
        slots := slots.modify np (·.push (8 * i + w))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  -- A tally bit is set exactly when the slice names that position, once per strike, so the whole
  -- tally is the slice itself shifted `nrec` times rather than a bit set per record.
  let mut seen := 0
  for w in [0:nrec] do
    seen := seen ||| (c <<< (w * len))
  let mut slotW := 16
  for k in [0:np + 1] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np + 1] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

/-- `stripeSort` over sixteen lanes a divisor, the twin of `stripeBatchHK`.

The lane takes four bits of the record rather than three, so the position has twelve left and a
batch holds at most 4096 divisors. Everything else is `stripeSort`: the same slices, the same
packing, and a tally of the same width, since sixteen lanes of `len` come to 65536 bits when `len`
is 4096 just as eight of 8192 do. -/
public def stripeSortH (s lo Wm1 start len W : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 65536
  let mut slots : Array (Array Nat) := Array.replicate (np + 1) #[]
  let mut slotAsm : Array Nat := Array.replicate np 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:16] do
      let X := (if w &&& 1 = 0 then b5 else b7) + (w >>> 1) * d
      if X ≤ Wm1 then
        slots := slots.modify (X >>> 16) (·.push (16 * i + w))
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
      else
        slots := slots.modify np (·.push (16 * i + w))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  let mut seen := 0
  for w in [0:16] do
    seen := seen ||| (c <<< (w * len))
  let mut slotW := 16
  for k in [0:np + 1] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np + 1] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

/-- `stripeSort` over two lanes a divisor, the twin of `stripeBatchLK` at `lw = 1`.

The widest band gives a divisor two strikes and so needs one lane bit, where the three-bit format
spends three and leaves thirteen for the position — a batch of 8192. At one bit the position gets
fifteen and a batch holds 32768. This exists to time that, nothing more. -/
public def stripeSortOne (s lo Wm1 start len W : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 65536
  let mut slots : Array (Array Nat) := Array.replicate (np + 1) #[]
  let mut slotAsm : Array Nat := Array.replicate np 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:2] do
      let X := if w == 0 then b5 else b7
      if X ≤ Wm1 then
        slots := slots.modify (X >>> 16) (·.push (2 * i + w))
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
      else
        slots := slots.modify np (·.push (2 * i + w))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  let mut seen := 0
  for w in [0:2] do
    seen := seen ||| (c <<< (w * len))
  let mut slotW := 16
  for k in [0:np + 1] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np + 1] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

/-- `stripeSort` over thirty-two lanes a divisor, the twin of `stripeBatchXK`. The lane takes five
bits of the record and the position eleven, so a batch holds at most 2048 divisors. -/
public def stripeSortX (s lo Wm1 start len W : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 65536
  let mut slots : Array (Array Nat) := Array.replicate (np + 1) #[]
  let mut slotAsm : Array Nat := Array.replicate np 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:32] do
      let X := (if w &&& 1 = 0 then b5 else b7) + (w >>> 1) * d
      if X ≤ Wm1 then
        slots := slots.modify (X >>> 16) (·.push (32 * i + w))
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
      else
        slots := slots.modify np (·.push (32 * i + w))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  let mut seen := 0
  for w in [0:32] do
    seen := seen ||| (c <<< (w * len))
  let mut slotW := 16
  for k in [0:np + 1] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np + 1] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

/-- `stripeSort` with the records whose strike falls past the window left out, and the tally
asking only for the ones that remain.

Screening only, and **not sound as it stands**: what stops a divisor being skipped is that the
tally accounts for every strike, and this accounts only for the strikes inside the window. It
exists to measure what dropping those records could be worth before the sound version is designed,
since that version needs a flag bit in the record, which would cap a batch at 4096 positions where
the length is tuned to 8192. -/
public def stripeSortW (s lo Wm1 start len W nrec : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 65536
  let mut slots : Array (Array Nat) := Array.replicate np #[]
  let mut slotAsm : Array Nat := Array.replicate np 0
  let mut seen := 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:nrec] do
      let X := (if w &&& 1 = 0 then b5 else b7) + (w >>> 1) * d
      if X ≤ Wm1 then
        slots := slots.modify (X >>> 16) (·.push (8 * i + w))
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
        -- The tally bit of a record that is kept, so the two sides ask for the same set.
        seen := seen ||| (1 <<< (i + w * len))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  let mut slotW := 16
  for k in [0:np] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

/-- `stripeSort` emitting only the records whose strike lands inside the window, with the last of
each progression flagged so that it accounts for the strikes after it.

A record is `flag` at bit 15, the position in bits 3 to 14, the strike in the low three, so a
batch holds at most 4096 positions. There is no out-of-window list. A progression with no strike
inside the window has nothing to flag, so its lanes are accounted for by flagging its first record
anyway, which the kernel accepts because that record's own strike is already past the end. -/
public def stripeSortG (s lo Wm1 start len W nrec : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let np := W / 65536
  let mut slots : Array (Array Nat) := Array.replicate np #[]
  let mut slotAsm : Array Nat := Array.replicate np 0
  let mut seen := 0
  let c := (s >>> start) &&& ((1 <<< len) - 1)
  for i in setBitsLow c len do
    let p := valueE (start + i)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    -- The two progressions are the even and odd lanes; each is walked until it leaves the window.
    for q in [0:2] do
      let b := if q = 0 then b5 else b7
      let lanes := (nrec + 1 - q) / 2
      let mut last := q
      let mut any := false
      for j in [0:lanes] do
        if b + j * d ≤ Wm1 then
          last := q + 2 * j
          any := true
      -- In this band a progression always has its first strike inside the window, since its start
      -- is below its period and the period is at most half the window. `any` is therefore always
      -- true here, and a progression with nothing inside would have no record to carry its tail.
      if !any then
        panic! "stripeSortG: a progression with no strike inside the window has no record to flag"
      for j in [0:lanes] do
        let w := q + 2 * j
        let X := b + j * d
        if X ≤ Wm1 then
          let flag := if w = last then 1 else 0
          let e := (flag <<< 15) ||| (i <<< 3) ||| w
          slots := slots.modify (X >>> 16) (·.push e)
          slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
          -- Each record speaks for its own lane, as the kernel's unflagged branch does.
          seen := seen ||| (1 <<< (i + w * len))
          if w = last then
            -- and the flagged one also for every later lane of its progression.
            for j2 in [0:lanes] do
              let w2 := q + 2 * j2
              if w2 ≥ w then
                seen := seen ||| (1 <<< (i + w2 * len))
  let mut asm := 0
  for k in [0:np] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  let mut slotW := 16
  for k in [0:np] do
    slotW := Nat.max slotW (16 * (slots[k]!).size)
  let mut ls := 0
  let mut cs := 0
  for k in [0:np] do
    let mut packed := 0
    for j in [0:(slots[k]!).size] do
      packed := packed ||| ((slots[k]!)[j]! <<< (16 * j))
    ls := ls ||| (packed <<< (slotW * k))
    cs := cs ||| ((slots[k]!).size <<< (16 * k))
  return (ls, cs, slotW, asm ||| (seen <<< W))

/-- Twin of `segLoopStripeK`. -/
public def segLoopStripe (s lo _Wm1 base acc start fuel : Nat) : Nat := Id.run do
  let mut a := acc
  for i in setBitsLow (s >>> start) fuel do
    let p := valueE (start + i)
    for X in [firstLoc (indexE (p * 5)) lo (p * 2), firstLoc (indexE (p * 7)) lo (p * 2)] do
      if base ≤ X && X - base ≤ 65535 then
        a := a ||| (1 <<< (X - base))
  return a

/-- Twin of `treeBatch2K`: the mask a batch of the widest band assembles. Built one slice at a
time and joined at the end, for the reason `stripeSort` is, since joining a bit straight into a
segment-wide accumulator rebuilds the whole number per record. -/
public def treeAsm2 (s lo Wm1 start len W : Nat) : Nat := Id.run do
  let nsl := W / 65536
  let mut slotAsm : Array Nat := Array.replicate nsl 0
  for j in setBitsLow (s >>> start) len do
    let p := valueE (start + j)
    for X in [firstLoc (indexE (p * 5)) lo (p * 2), firstLoc (indexE (p * 7)) lo (p * 2)] do
      if X ≤ Wm1 then
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
  let mut asm := 0
  for k in [0:nsl] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  return asm

/-- Twin of `treeBatch4K` and `treeBatchK`: the mask a batch assembles when each divisor places
`nrec` strikes. Built one 65536-bit slice at a time and joined at the end. -/
public def treeAsmN (s lo Wm1 start len W nrec : Nat) : Nat := Id.run do
  let nsl := W / 65536
  let mut slotAsm : Array Nat := Array.replicate nsl 0
  for j in setBitsLow (s >>> start) len do
    let p := valueE (start + j)
    let d := p * 2
    let b5 := firstLoc (indexE (p * 5)) lo d
    let b7 := firstLoc (indexE (p * 7)) lo d
    for w in [0:nrec] do
      let X := (if w &&& 1 = 0 then b5 else b7) + (w >>> 1) * d
      if X ≤ Wm1 then
        slotAsm := slotAsm.modify (X >>> 16) (· ||| (1 <<< (X &&& 65535)))
  let mut asm := 0
  for k in [0:nsl] do
    asm := asm ||| ((slotAsm[k]!) <<< (k * 65536))
  return asm

/-- Twin of `segMarkRK`. -/
public def segMarkR (seg p lo Wm1 : Nat) : Nat :=
  let A := firstLoc (indexE (p * 5)) lo (p * 2)
  let B := firstLoc (indexE (p * 7)) lo (p * 2)
  let hit := buildMaskR p Wm1 A B &&& seg
  if hit = 0 then seg else seg - hit

/-- Twin of `segLoopSRK`. -/
public def segLoopR (s lo Wm1 seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in setBitsLow (s >>> start) fuel do
    b := segMarkR b (valueE (start + i)) lo Wm1
  return b

/-- Twin of `segMarkNK`. -/
public def segMarkN (seg p lo Wm1 n : Nat) : Nat :=
  let A := firstLoc (indexE (p * 5)) lo (p * 2)
  let B := firstLoc (indexE (p * 7)) lo (p * 2)
  let hit := buildMaskN p Wm1 A B n &&& seg
  if hit = 0 then seg else seg - hit

/-- Twin of `segLoopSNK`, reading the base primes from the batch's own slice. -/
public def segLoopN (s lo Wm1 n seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in setBitsLow (s >>> start) fuel do
    b := segMarkN b (valueE (start + i)) lo Wm1 n
  return b

/-- Twin of `segAccLoopK`, joining the batch's masks into the running accumulator. -/
public def segAccLoopC (s lo Wm1 n acc start fuel : Nat) : Nat := Id.run do
  let mut a := acc
  for i in setBitsLow (s >>> start) fuel do
    let p := valueE (start + i)
    let A := firstLoc (indexE (p * 5)) lo (p * 2)
    let B := firstLoc (indexE (p * 7)) lo (p * 2)
    a := a ||| buildMaskC p Wm1 A B n
  return a

/-- Join a list of `w0`-bit pieces, least significant first, into one number, combining them in
pairs rather than shifting each into a full-width accumulator. The loop is bounded by 64 rounds,
which covers any array this file builds. -/
public def joinWords (ws : Array Nat) (w0 : Nat) : Nat := Id.run do
  let mut cur := ws
  let mut width := w0
  for _ in [0:64] do
    if cur.size > 1 then
      let mut nxt : Array Nat := Array.emptyWithCapacity ((cur.size + 1) / 2)
      let mut i := 0
      for _ in [0:(cur.size + 1) / 2] do
        if i + 1 < cur.size then
          nxt := nxt.push (cur[i]! ||| (cur[i + 1]! <<< width))
        else if i < cur.size then
          nxt := nxt.push cur[i]!
        i := i + 2
      cur := nxt
      width := width * 2
  return if cur.isEmpty then 0 else cur[0]!

/-- The number a byte array holds, least significant byte first. -/
public def bytesToNat (ba : ByteArray) : Nat := Id.run do
  let words := (ba.size + 7) / 8
  let mut ws : Array Nat := Array.emptyWithCapacity words
  let mut i := 0
  for _ in [0:words] do
    let mut w : Nat := 0
    for b in [0:8] do
      if i + b < ba.size then
        w := w ||| ((ba.get! (i + b)).toNat <<< (8 * b))
    ws := ws.push w
    i := i + 8
  return joinWords ws 64

/-- What `segLoopC` returns, reached through a byte array instead of through masks.

The emitter is not trusted: the kernel checks the literal this produces against `segLoopCK`, so
this only has to agree, not to agree for the same reason. Clearing a divisor's bits one at a time
and clearing the union of every divisor's bits come to the same window, so the strikes go into a
byte array a bit at a time and the whole batch costs one `land` and one `sub` on a window-wide
number rather than a mask built and applied per divisor.

The progression a divisor contributes is every `b + j * 2p` up to `Wm1`, from each of its two
starting positions. `buildMaskC` reaches exactly those: its rounds double while `2^(i+1) * p` fits
in `Wm1`, and `nb` in `runSegmentV` is chosen so the doubling covers the batch's smallest
divisor. Bits it places above `Wm1` are dropped when the mask meets the window. -/
public def segLoopCBytes (s lo Wm1 seg start fuel : Nat) : Nat := Id.run do
  let mut ba := ByteArray.mk (Array.replicate (Wm1 / 8 + 1) 0)
  for i in setBitsLow (s >>> start) fuel do
    let p := valueE (start + i)
    let d := p * 2
    for b in [firstLoc (indexE (p * 5)) lo d, firstLoc (indexE (p * 7)) lo d] do
      if b ≤ Wm1 then
        let mut X := b
        for _ in [0:(Wm1 - b) / d + 1] do
          ba := ba.set! (X >>> 3) (ba.get! (X >>> 3) ||| UInt8.ofNat (1 <<< (X &&& 7)))
          X := X + d
  let mask := bytesToNat ba
  return seg - (mask &&& seg)

/-! ## A mask built to the window's width

Twins of `buildMaskEK` and `segLoopEK`, together with the choice of round count and final shift
those take as arguments. Nothing here is trusted: `runSegmentV` checks the window this produces
against the window `segLoopC` produces and refuses to emit if they differ. -/

/-- Interleave two `h`-bit numbers, `a` onto the even positions and `b` onto the odd ones.

Done by halving rather than a bit at a time: reading bit `j` of a window-sized number costs a pass
over the whole number, so a bit-at-a-time interleave is quadratic in the width and will not finish
at the sizes the sieve runs at. `fuel` bounds the halving and needs only to reach `h ≤ 32`. -/
public def interleaveB : Nat → Nat → Nat → Nat → Nat
  | 0, h, a, b => Id.run do
    let mut r := 0
    for j in [0:h] do
      if (a >>> j) &&& 1 == 1 then r := r ||| (1 <<< (2 * j))
      if (b >>> j) &&& 1 == 1 then r := r ||| (1 <<< (2 * j + 1))
    return r
  | fuel + 1, h, a, b =>
    if h ≤ 32 then interleaveB 0 h a b
    else
      let g := h / 2
      let m := (1 <<< g) - 1
      interleaveB fuel g (a &&& m) (b &&& m) |||
        (interleaveB fuel (h - g) (a >>> g) (b >>> g)) <<< (2 * g)

/-- Take `h` even positions and `h` odd ones apart, the inverse of `interleaveB`. -/
public def deinterleaveB : Nat → Nat → Nat → Nat × Nat
  | 0, h, x => Id.run do
    let mut a := 0
    let mut b := 0
    for j in [0:h] do
      if (x >>> (2 * j)) &&& 1 == 1 then a := a ||| (1 <<< j)
      if (x >>> (2 * j + 1)) &&& 1 == 1 then b := b ||| (1 <<< j)
    return (a, b)
  | fuel + 1, h, x =>
    if h ≤ 32 then deinterleaveB 0 h x
    else
      let g := h / 2
      let lo := deinterleaveB fuel g (x &&& ((1 <<< (2 * g)) - 1))
      let hi := deinterleaveB fuel (h - g) (x >>> (2 * g))
      (lo.1 ||| (hi.1 <<< g), lo.2 ||| (hi.2 <<< g))

/-- Split a window into its even positions and its odd ones, the evens in the low half. -/
public def splitWindow (seg W : Nat) : Nat :=
  let h := W / 2
  let ab := deinterleaveB 32 h seg
  ab.1 ||| (ab.2 <<< h)

/-- Put a split window back the way it was, so the two can be compared. -/
public def joinWindow (sp W : Nat) : Nat :=
  let h := W / 2
  interleaveB 32 h (sp &&& ((1 <<< h) - 1)) (sp >>> h)

/-- Twin of `splitLoopK`. -/
public def splitLoop (s lo H n seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in setBitsLow (s >>> start) fuel do
    let p := valueE (start + i)
    let A := firstLoc (indexE (p * 5)) lo (p * 2)
    let B := firstLoc (indexE (p * 7)) lo (p * 2)
    let aA := (if A % 2 == 0 then A else B) / 2
    let aB := ((if A % 2 == 0 then B else A) - 1) / 2
    let mut c := 1
    for i2 in [0:n] do
      let sh := p <<< i2
      if sh ≤ H - 1 then
        c := c ||| (c <<< sh)
    -- Clamped to a half each. The undivided window has no bits past its end, so a mask running
    -- over does no harm there; here the low half's overflow would land on the high half.
    let full := (1 <<< H) - 1
    let mask := ((c <<< aA) &&& full) ||| (((c <<< aB) &&& full) <<< H)
    let hit := b &&& mask
    if hit != 0 then b := b - hit
  return b

/-- Twin of `buildCompK`: one period with the two strikes cleared, tiled by doubling. -/
public def buildComp (p M A B n : Nat) : Nat := Id.run do
  let mut m := ((1 <<< (p * 2)) - 1) - (1 <<< A) - (1 <<< B)
  for i in [0:n] do
    let sh := p <<< (i + 1)
    if sh ≤ M then
      m := m ||| (m <<< sh)
  return m

/-- Twin of `segLoopKeepK`. -/
public def segLoopKeep (s lo Wm1 n seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in setBitsLow (s >>> start) fuel do
    let p := valueE (start + i)
    let A := firstLoc (indexE (p * 5)) lo (p * 2)
    let B := firstLoc (indexE (p * 7)) lo (p * 2)
    b := b &&& buildComp p Wm1 A B n
  return b

/-! ## Pricing a gcd certificate

An idea worth a number before it is worth a design: instead of a mask for every divisor, sieve by
the small ones only and let one `Nat.gcd` per slice certify that nothing left in that slice has a
factor in the rest of the range. The kernel's `gcd` is on its fast path, so the statement needs no
new definitions, but nobody knows what a gcd of these sizes costs. These build the two numbers at
the sizes the real design would use, so a probe can time it. -/

/-- The product of the primes in `(lo, hi]`, read off a base sieve bitset. -/
public def primorialOver (s lo hi : Nat) : Nat := Id.run do
  let mut acc := 1
  let mut i := 1
  for _ in [0:hi] do
    let p := valueE i
    if p > hi then
      break
    if p > lo && (s >>> i) &&& 1 == 1 then
      acc := acc * p
    i := i + 1
  return acc

/-- The product of the window positions still set in one 65536-bit slice. -/
public def sliceProduct (bits lo k : Nat) : Nat := Id.run do
  let slice := (bits >>> (k * 65536)) &&& ((1 <<< 65536) - 1)
  let mut acc := 1
  for j in setBitsLow slice 65536 do
    acc := acc * valueE (lo + k * 65536 + j)
  return acc

/-- Twin of `comboMaskK`: the union of 5, 7, 11 and 13 built once at their shared period of 10010
positions and then tiled to the window. -/
public def comboMask (lo M : Nat) : Nat := Id.run do
  let mut base := 0
  for p in [5, 7, 11, 13] do
    let A := firstLoc (indexE (p * 5)) lo (p * 2)
    let B := firstLoc (indexE (p * 7)) lo (p * 2)
    base := base ||| buildMaskC p 10009 A B 14
  let mut m := base
  for i in [0:12] do
    let sh := 10010 <<< i
    if sh ≤ M then
      m := m ||| (m <<< sh)
  return m

/-- Twin of `comboClearK`. -/
public def comboClear (seg lo M : Nat) : Nat :=
  let hit := seg &&& comboMask lo M
  if hit = 0 then seg else seg - hit

/-- Twin of `spanEK`. -/
public def spanE (p M n : Nat) : Nat := Id.run do
  let mut s := p * 2
  for i in [0:n] do
    if (p <<< (i + 2)) ≤ M + 1 then
      s := s * 2
  return s

/-- Twin of `shiftEK`. -/
public def shiftE (p M n : Nat) : Nat :=
  (p * 2) * ((M + 1 - spanE p M n + (p * 2 - 1)) / (p * 2))

/-- Twin of `buildMaskEK`. -/
public def buildMaskE (p M A B n : Nat) : Nat := Id.run do
  let mut m := seedC A M ||| seedC B M
  for i in [0:n] do
    if (p <<< (i + 2)) ≤ M + 1 then
      m := m ||| (m <<< (p <<< (i + 1)))
  return m ||| (m <<< shiftE p M n)

/-- Twin of `segMarkEK`. -/
public def segMarkE (seg p lo Wm1 n : Nat) : Nat :=
  let A := firstLoc (indexE (p * 5)) lo (p * 2)
  let B := firstLoc (indexE (p * 7)) lo (p * 2)
  let mask := if p * 2 ≤ Wm1 then buildMaskE p Wm1 A B n else seedC A Wm1 ||| seedC B Wm1
  let hit := seg &&& mask
  if hit = 0 then seg else seg - hit

/-- Twin of `segLoopEK`. -/
public def segLoopE (s lo Wm1 n seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in setBitsLow (s >>> start) fuel do
    b := segMarkE b (valueE (start + i)) lo Wm1 n
  return b

/-- Twin of `segAccLoopEK`. -/
public def segAccLoopE (s lo Wm1 n acc start fuel : Nat) : Nat := Id.run do
  let mut a := acc
  for i in setBitsLow (s >>> start) fuel do
    let p := valueE (start + i)
    let A := firstLoc (indexE (p * 5)) lo (p * 2)
    let B := firstLoc (indexE (p * 7)) lo (p * 2)
    a := a ||| buildMaskE p Wm1 A B n
  return a

/-! ## The thirty wheel's twins

Prototype, matching the kernel definitions of the same names. Nothing here is proved sound; it
produces the literals a timing run checks. -/

/-- The eight residues coprime to 30, five bits each. -/
public def wheel30Offs : Nat := 1021784272097

/-- Where each residue modulo 30 sits among those eight, three bits each. -/
public def wheel30Rank : Nat := 1083201076879154698854072320

/-- The eight multipliers a divisor's progressions start from, five bits each. -/
public def wheel30Mul : Nat := 1097082647911

/-- The `k`th integer coprime to 30. -/
public def value30 (k : Nat) : Nat :=
  30 * (k / 8) + ((wheel30Offs >>> (5 * (k % 8))) &&& 31)

/-- Where an integer coprime to 30 sits in that enumeration. -/
public def index30 (q : Nat) : Nat :=
  8 * (q / 30) + ((wheel30Rank >>> (3 * (q % 30))) &&& 7)

/-- Twin of `seeds30K`. -/
public def seeds30 (p lo M : Nat) : Nat := Id.run do
  let mut a := 0
  for j in [0:8] do
    let m := (wheel30Mul >>> (5 * j)) &&& 31
    a := a ||| seedC (firstLoc (index30 (p * m)) lo (p * 8)) M
  return a

/-- Twin of `buildMask30CK`. -/
public def buildMask30C (p M lo n : Nat) : Nat := Id.run do
  let mut m := seeds30 p lo M
  for i in [0:n] do
    let sh := p <<< (i + 3)
    if sh ≤ M then
      m := m ||| (m <<< sh)
  return m

/-- Twin of `segMark30CK`. -/
public def segMark30C (seg p lo Wm1 n : Nat) : Nat :=
  let mask := if p * 8 ≤ Wm1 then buildMask30C p Wm1 lo n else seeds30 p lo Wm1
  let hit := mask &&& seg
  if hit = 0 then seg else seg - hit

/-- Twin of `segLoop30CK`. -/
public def segLoop30C (s lo Wm1 n seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in setBitsLow (s >>> start) fuel do
    b := segMark30C b (valueE (start + i)) lo Wm1 n
  return b

/-- Twin of `segLoopCK`, reading the base primes from the batch's own slice of the base sieve.
Every batch literal in `runSegmentV` comes from here, and `segLoopK` and `segLoopCK` agree on all
of them: the seeds and rounds this drops carry bits above `Wm1` only, which `seg` never holds. -/
public def segLoopC (s lo Wm1 n seg start fuel : Nat) : Nat := Id.run do
  let mut b := seg
  for i in setBitsLow (s >>> start) fuel do
    b := segMarkC b (valueE (start + i)) lo Wm1 n
  return b

/-- `segLoopC` that also returns which divisors cleared a bit.

A divisor whose mask meets nothing live leaves the window exactly as it found it, so dropping it
changes neither the result nor the state any later divisor sees, and by induction the window built
from the divisors returned here is the one every divisor builds. That is what lets the sieve mark a
subset and certify the rest.

Which divisors those are needs no separate pass: `segMarkC` already forms `hit` and compares it to
zero to decide whether to subtract, so this records the comparison it was making anyway. The
alternative, asking each divisor in turn against a fixed earlier state, builds one window-wide mask
per divisor on top of the marking the emitter does regardless.

Live is taken here in the order the loop runs, rather than against a fixed prefix, which needs no
threshold: a divisor that meets nothing live when its turn comes meets nothing in the finished
window either, since marking only ever clears bits.

The bitmask is accumulated a block at a time and joined once at the end. Setting each bit straight
into one number would shift and or a number as wide as the divisor range on every hit, and there
are as many hits as divisors that strike. -/
public def segLoopHits (s lo Wm1 n seg start fuel : Nat) : Nat × Nat × Nat × Nat := Id.run do
  let blk := 4096
  let nblk := (start + fuel) / blk + 1
  let mut acc : Array Nat := Array.replicate nblk 0
  let mut b := seg
  let mut nHit := 0
  let mut nTot := 0
  for i in setBitsLow (s >>> start) fuel do
    nTot := nTot + 1
    let nxt := segMarkC b (valueE (start + i)) lo Wm1 n
    if nxt != b then
      nHit := nHit + 1
      let j := start + i
      acc := acc.modify (j / blk) (· ||| (1 <<< (j % blk)))
      b := nxt
  let mut hits := 0
  for j in [0:nblk] do
    hits := hits ||| ((acc[nblk - 1 - j]!) <<< ((nblk - 1 - j) * blk))
  return (b, hits, nHit, nTot)

/-- Which divisors of the widest band strike a bit that is still live in `base`.

Returns the bitmask of those divisors, how many there were, and how many were tested. `first` and
`last` bound the band in divisor indices, and `base` is the window after the other three bands have
been marked.

**The band's divisors have at most two strikes each**, since `Wm1 < 2p` puts the second term of
each progression past the end of the window, so a divisor is tested by looking at two positions
rather than by building a mask. That is the whole point: `segLoopC` over every divisor costs 124 s
a window, where the band holding 87.5% of the skippable divisors is 1017936 positions.

**Liveness is read out of a flat array, not by `testBit` on `base`.** `base.testBit k` shifts a
4.19 Mbit number to reach one bit, so a million of them repeats the mistake that `setBitsLow` makes
with a large `len`. Instead each 65536-bit slice is taken down once and `setBitsLow` enumerates its
live bits, 1024 iterations a slice, and the positions go into an array that answers in one step.

**No ordering.** A divisor here is tested against a fixed `base` rather than against the window as
this band marks it. Counted on the production window, that marks exactly the same 73742 divisors as
testing in order, and it can only ever mark extra ones, never miss a striker, so the window it
builds is unchanged either way. -/
public def wideHits (s lo Wm1 base first last : Nat) : Nat × Nat × Nat := Id.run do
  let mut live : Array Bool := Array.replicate (Wm1 + 1) false
  let np := (Wm1 + 1) / 65536
  for k in [0:np] do
    let slice := (base >>> (k * 65536)) &&& ((1 <<< 65536) - 1)
    for b in setBitsLow slice 65536 do
      live := live.set! (k * 65536 + b) true
  let blk := 4096
  let nblk := last / blk + 2
  let mut acc : Array Nat := Array.replicate nblk 0
  let mut nHit := 0
  let mut nTot := 0
  -- Taken in batches of 8192, and the set divisors of each batch enumerated once. Asking
  -- `(s >>> i) &&& 1` per divisor would shift a 3.3 Mbit number half a million times, and a single
  -- `setBitsLow` over the whole band would walk a 500 kbit number word by word; both are the trap
  -- this function exists to avoid.
  let count := last + 1 - first
  for c in [0:(count + 8191) / 8192] do
    let start := first + c * 8192
    let stepN := Nat.min 8192 (count - c * 8192)
    for off in setBitsLow (s >>> start) stepN do
      let i := start + off
      nTot := nTot + 1
      let p := valueE i
      let A := firstLoc (indexE (p * 5)) lo (p * 2)
      let B := firstLoc (indexE (p * 7)) lo (p * 2)
      let hitA := A ≤ Wm1 && live[A]!
      let hitB := B ≤ Wm1 && live[B]!
      if hitA || hitB then
        nHit := nHit + 1
        acc := acc.modify (i / blk) (· ||| (1 <<< (i % blk)))
  let mut hits := 0
  for j in [0:nblk] do
    hits := hits ||| ((acc[nblk - 1 - j]!) <<< ((nblk - 1 - j) * blk))
  return (hits, nHit, nTot)

end SieveEmit
