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
position; peeling 64 bits at a time leaves the bit tests inside a single word. -/
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

end SieveEmit
