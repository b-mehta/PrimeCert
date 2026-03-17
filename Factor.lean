/-! # Fast integer factorization executable

Trial division + Miller-Rabin + Pollard-Brent rho + ECM.
Uses unboxed UInt64 FFI for numbers < 2^63, GMP-backed Nat for larger.

Usage: lake exe factor <number>
Output: one "prime exponent" pair per line, sorted.
-/

-- ============================================================
-- FFI: unboxed 64-bit modular arithmetic (zero allocation)
-- ============================================================

@[extern "lean_mulmod64"]
opaque mulMod64 (a b m : UInt64) : UInt64

@[extern "lean_submod64"]
opaque subMod64 (a b m : UInt64) : UInt64

-- UInt64 modular exponentiation (fully unboxed)
@[inline] partial def powMod64 (base exp m : UInt64) : UInt64 :=
  go (base % m) exp 1
where
  @[inline] go (b e acc : UInt64) : UInt64 :=
    if e = 0 then acc
    else
      let acc' := if e &&& 1 = 1 then mulMod64 acc b m else acc
      go (mulMod64 b b m) (e >>> 1) acc'

-- UInt64 GCD (unboxed)
@[inline] partial def gcd64 (a b : UInt64) : UInt64 :=
  if b = 0 then a else gcd64 b (a % b)

-- UInt64 Miller-Rabin (fully unboxed inner loop)
def millerRabin64 (n a : UInt64) : Bool := Id.run do
  if a % n = 0 then return false
  let mut d := n - 1
  let mut r : UInt64 := 0
  while d &&& 1 = 0 do d := d >>> 1; r := r + 1
  let mut x := powMod64 a d n
  if x = 1 || x = n - 1 then return false
  let mut i : UInt64 := 0
  while i < r - 1 do
    x := mulMod64 x x n
    if x = n - 1 then return false
    i := i + 1
  return true

def isPrime64 (n : UInt64) : Bool :=
  if n < 2 then false
  else if n < 4 then true
  else if n &&& 1 = 0 || n % 3 = 0 then false
  else !(millerRabin64 n 2 || millerRabin64 n 3 || millerRabin64 n 5 ||
         millerRabin64 n 7 || millerRabin64 n 11 || millerRabin64 n 13 ||
         millerRabin64 n 17 || millerRabin64 n 19 || millerRabin64 n 23 ||
         millerRabin64 n 29 || millerRabin64 n 31 || millerRabin64 n 37)

-- UInt64 Pollard-Brent rho (fully unboxed — zero allocation in hot loop)
structure Rng where state : UInt64 deriving Inhabited

@[inline] def Rng.next (rng : Rng) : Rng × UInt64 :=
  let s := rng.state ^^^ (rng.state <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ({ state := s }, s)

partial def pollardRho64 (n : UInt64) (rng : Rng) (maxAttempts : Nat) :
    Option UInt64 × Rng := Id.run do
  if n &&& 1 = 0 then return (some 2, rng)
  let mut rng := rng
  for _ in List.range maxAttempts do
    let (r1, cv) := rng.next
    let c := cv % (n - 1) + 1
    let (r2, yv) := r1.next
    rng := r2
    let mut y := yv % n
    let mut q : UInt64 := 1
    let mut g : UInt64 := 1
    let mut r : Nat := 1
    let mut x : UInt64 := 0
    let mut ys : UInt64 := 0
    while g = 1 do
      x := y
      for _ in List.range r do
        y := mulMod64 y y n + c
        if y ≥ n then y := y - n
      let mut k : Nat := 0
      while k < r && g = 1 do
        ys := y
        let bound := min 128 (r - k)
        for _ in List.range bound do
          y := mulMod64 y y n + c
          if y ≥ n then y := y - n
          q := mulMod64 q (if x ≥ y then x - y else y - x) n
        g := gcd64 q n
        k := k + bound
      r := r * 2
      if r > 4000000 then break
    if g = n then
      g := 1
      while g = 1 do
        ys := mulMod64 ys ys n + c
        if ys ≥ n then ys := ys - n
        g := gcd64 (if x ≥ ys then x - ys else ys - x) n
    if g != n && g != 1 then return (some g, rng)
  return (none, rng)

-- ============================================================
-- Nat path (for numbers ≥ 2^63)
-- ============================================================

partial def powModNat (base exp n : Nat) : Nat :=
  if n ≤ 1 then 0
  else go (base % n) exp 1
where
  go (b e acc : Nat) : Nat :=
    if e = 0 then acc
    else
      let acc' := if e &&& 1 = 1 then acc * b % n else acc
      go (b * b % n) (e >>> 1) acc'

def millerRabinNat (n a : Nat) : Bool := Id.run do
  if a % n = 0 then return false
  let mut d := n - 1
  let mut r := 0
  while d &&& 1 = 0 do d := d >>> 1; r := r + 1
  let mut x := powModNat a d n
  if x = 1 || x = n - 1 then return false
  for _ in List.range r do
    x := x * x % n
    if x = n - 1 then return false
  return true

def isPrimeNat (n : Nat) : Bool :=
  if n < 2 then false
  else if n < 4 then true
  else if n &&& 1 = 0 || n % 3 = 0 then false
  else #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37].all fun a => !millerRabinNat n a

partial def pollardRhoNat (n : Nat) (rng : Rng) (maxAttempts : Nat) :
    Option Nat × Rng := Id.run do
  if n &&& 1 = 0 then return (some 2, rng)
  let mut rng := rng
  for _ in List.range maxAttempts do
    let (r1, cv) := rng.next
    let c := cv.toNat % (n - 1) + 1
    let (r2, yv) := r1.next
    rng := r2
    let mut y := yv.toNat % n
    let mut q : Nat := 1
    let mut g : Nat := 1
    let mut r : Nat := 1
    let mut x : Nat := 0
    let mut ys : Nat := 0
    while g = 1 do
      x := y
      for _ in List.range r do y := (y * y + c) % n
      let mut k : Nat := 0
      while k < r && g = 1 do
        ys := y
        let bound := min 128 (r - k)
        for _ in List.range bound do
          y := (y * y + c) % n
          q := q * (if x ≥ y then x - y else y - x) % n
        g := Nat.gcd q n
        k := k + bound
      r := r * 2
      if r > 2000000 then break
    if g = n then
      g := 1
      while g = 1 do
        ys := (ys * ys + c) % n
        g := Nat.gcd (if x ≥ ys then x - ys else ys - x) n
    if g != n && g != 1 then return (some g, rng)
  return (none, rng)

-- ============================================================
-- Dispatch: UInt64 for < 2^63, Nat for larger
-- ============================================================

def smallBound : Nat := 1 <<< 63

def isPrime (n : Nat) : Bool :=
  if n < smallBound then isPrime64 n.toUInt64 else isPrimeNat n

def pollardRho (n : Nat) (rng : Rng) (attempts : Nat) : Option Nat × Rng :=
  if n < smallBound then
    let (r, rng') := pollardRho64 n.toUInt64 rng attempts
    (r.map UInt64.toNat, rng')
  else pollardRhoNat n rng attempts

-- ============================================================
-- ECM (uses Nat — only called for numbers > 2^63)
-- ============================================================

structure ECMPoint where (x z : Nat) deriving Inhabited

@[inline] def subMod (a b n : Nat) : Nat :=
  if a ≥ b then (a - b) % n else (a + n - b) % n

def ecmDouble (P : ECMPoint) (a24 n : Nat) : ECMPoint :=
  let u := (P.x + P.z) % n * ((P.x + P.z) % n) % n
  let v := subMod P.x P.z n * (subMod P.x P.z n) % n
  let rx := u * v % n
  let diff := subMod u v n
  let rz := (a24 * diff % n + v) % n * diff % n
  { x := rx, z := rz }

def ecmAdd (P Q D : ECMPoint) (n : Nat) : ECMPoint :=
  let u := subMod P.x P.z n * ((Q.x + Q.z) % n) % n
  let v := (P.x + P.z) % n * (subMod Q.x Q.z n) % n
  let su := (u + v) % n * ((u + v) % n) % n
  let di := subMod u v n * (subMod u v n) % n
  { x := D.z * su % n, z := D.x * di % n }

partial def ecmMul (P : ECMPoint) (k : Nat) (a24 n : Nat) : ECMPoint :=
  if k = 0 then { x := 0, z := 0 }
  else if k = 1 then P
  else
    let topBit := Nat.log2 k
    go P (ecmDouble P a24 n) (topBit - 1)
where
  go (R Q : ECMPoint) (bit : Nat) : ECMPoint :=
    let R' := if k &&& (1 <<< bit) != 0
      then ecmAdd Q R P n else ecmDouble R a24 n
    let Q' := if k &&& (1 <<< bit) != 0
      then ecmDouble Q a24 n else ecmAdd R Q P n
    if bit = 0 then R' else go R' Q' (bit - 1)

def smallPrimes : Array Nat := Id.run do
  let mut ps : Array Nat := #[2]
  let mut n := 3
  while n < 1100 do
    let mut c := false
    let mut d := 3
    while d * d ≤ n do
      if n % d = 0 then c := true; break
      d := d + 2
    if !c then ps := ps.push n
    n := n + 2
  return ps

partial def ecmOneCurve (n : Nat) (sigma : Nat) (B1 : Nat) : Option Nat := Id.run do
  let u := subMod (sigma * sigma % n) 5 n
  let v := (sigma * 4) % n
  let px := u * u % n * u % n
  let pz := v * v % n * v % n
  let mut P : ECMPoint := { x := px, z := pz }
  let diff := subMod v u n
  let num := diff * diff % n * diff % n * ((u * 3 + v) % n) % n
  let den := px * v % n * 16 % n
  let g := Nat.gcd den n
  if g != 1 then return if g != n then some g else none
  let inv := modInverse den n
  let a24 := num * inv % n

  -- Stage 1
  for p in smallPrimes do
    if p > B1 then break
    let mut pp := p
    while pp ≤ B1 / p do pp := pp * p
    P := ecmMul P pp a24 n
  let mut p := 1009
  while p ≤ B1 do
    let mut c := false
    let mut d := 3
    while d * d ≤ p do
      if p % d = 0 then c := true; break
      d := d + 2
    if !c then
      let mut pp := p
      while pp ≤ B1 / p do pp := pp * p
      P := ecmMul P pp a24 n
    p := p + 2

  let g := Nat.gcd P.z n
  if g != 1 && g != n then return some g

  -- Stage 2
  let B2 := B1 * 10
  let P2 := ecmDouble P a24 n
  let startQ := if B1 % 2 = 0 then B1 + 1 else B1
  let mut Q := ecmMul P startQ a24 n
  let mut Qprev := ecmMul P (startQ - 2) a24 n
  let mut acc : Nat := 1
  let mut q := startQ
  while q ≤ B2 do
    let mut isP := q > 1 && q &&& 1 = 1
    if isP then
      let mut d := 3
      while d * d ≤ q do
        if q % d = 0 then isP := false; break
        d := d + 2
    if isP then acc := acc * Q.z % n
    let Qnext := ecmAdd Q P2 Qprev n
    Qprev := Q; Q := Qnext; q := q + 2
    if q % 2000 < 2 then
      let g2 := Nat.gcd acc n
      if g2 != 1 && g2 != n then return some g2
      acc := 1
  let g2 := Nat.gcd acc n
  if g2 != 1 && g2 != n then return some g2
  return none
where
  modInverse (a n : Nat) : Nat := Id.run do
    let mut old_r : Int := a; let mut r : Int := n
    let mut old_s : Int := 1; let mut s : Int := 0
    while r != 0 do
      let q := old_r / r
      let t := r; r := old_r - q * r; old_r := t
      let t := s; s := old_s - q * s; old_s := t
    if old_r != 1 then return 0
    return (old_s % n).toNat

partial def ecm (n : Nat) (B1 : Nat) (curves : Nat) (rng : Rng) : Option Nat × Rng := Id.run do
  let mut rng := rng
  for _ in List.range curves do
    let (rng', sv) := rng.next; rng := rng'
    match ecmOneCurve n (sv.toNat % 1000000 + 6) B1 with
    | some d => return (some d, rng)
    | none => pure ()
  return (none, rng)

-- ============================================================
-- Trial division + full factorization
-- ============================================================

def trialDivide (n : Nat) : Array (Nat × Nat) × Nat := Id.run do
  let mut fs : Array (Nat × Nat) := #[]
  let mut n := n
  for p in #[2, 3, 5] do
    let mut e := 0
    while n % p = 0 do e := e + 1; n := n / p
    if e > 0 then fs := fs.push (p, e)
  let mut p := 7
  while p ≤ 1000000 && p * p ≤ n do
    for step in #[0, 4] do
      let q := p + step
      let mut e := 0
      while n % q = 0 do e := e + 1; n := n / q
      if e > 0 then fs := fs.push (q, e)
    p := p + 6
  return (fs, n)

def addFactor (fs : Array (Nat × Nat)) (p : Nat) : Array (Nat × Nat) :=
  match fs.findIdx? (fun (q, _) => q = p) with
  | some i => fs.set! i (p, (fs[i]!).2 + 1)
  | none => fs.push (p, 1)

partial def factorize (n : Nat) : Array (Nat × Nat) := Id.run do
  if n ≤ 1 then return #[]
  let (trialFs, remaining) := trialDivide n
  let mut fs := trialFs
  let mut stack : Array Nat := if remaining > 1 then #[remaining] else #[]
  let mut rng : Rng := { state := 42 }
  while stack.size > 0 do
    let m := stack.back!
    stack := stack.pop
    if m ≤ 1 then continue
    if isPrime m then
      fs := addFactor fs m; continue
    let digits := (toString m).length
    let rhoAttempts := if digits ≤ 30 then 50 else if digits ≤ 40 then 3 else 1
    let (rhoResult, rng') := pollardRho m rng rhoAttempts
    rng := rng'
    match rhoResult with
    | some d => stack := stack.push d; stack := stack.push (m / d); continue
    | none => pure ()
    let params := #[(2000, 25), (10000, 200), (50000, 300), (250000, 500)]
    let mut found := false
    for (b1, curves) in params do
      let (r, rng') := ecm m b1 curves rng; rng := rng'
      match r with
      | some d => stack := stack.push d; stack := stack.push (m / d); found := true; break
      | none => pure ()
    if !found then
      let (r, rng') := pollardRho m rng 100; rng := rng'
      match r with
      | some d => stack := stack.push d; stack := stack.push (m / d)
      | none => fs := addFactor fs m
  return fs.qsort (fun a b => a.1 < b.1)

def main (args : List String) : IO Unit := do
  match args with
  | [nStr] =>
    match nStr.toNat? with
    | some n =>
      for (p, e) in factorize n do
        IO.println s!"{p} {e}"
    | none => IO.eprintln s!"Invalid number: {nStr}"
  | _ => IO.eprintln "Usage: factor <number>"
