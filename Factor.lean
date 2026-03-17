/-! # Fast integer factorization executable

Trial division + Miller-Rabin + Pollard-Brent rho + ECM.
Uses unboxed UInt64 FFI for < 2^63, GMP FFI (rho+ECM) for larger.

Usage: lake exe factor <number>
Output: one "prime exponent" pair per line, sorted.
-/

-- ============================================================
-- FFI declarations
-- ============================================================

-- Unboxed 64-bit modular multiply via __int128 (ffi/mulmod.c)
@[extern "lean_mulmod64"] opaque mulMod64 (a b m : UInt64) : UInt64
@[extern "lean_submod64"] opaque subMod64 (a b m : UInt64) : UInt64

-- GMP-backed rho+ECM for large numbers (ffi/factor_ffi.c)
@[extern "lean_factor_rho"] opaque factorFFI (n : @& Nat) : Option Nat
@[extern "lean_is_prime_gmp"] opaque isPrimeGMP (n : @& Nat) : Bool

-- ============================================================
-- UInt64 fast path (fully unboxed, zero allocation)
-- ============================================================

@[inline] partial def powMod64 (base exp m : UInt64) : UInt64 :=
  go (base % m) exp 1
where
  @[inline] go (b e acc : UInt64) : UInt64 :=
    if e = 0 then acc
    else go (mulMod64 b b m) (e >>> 1) (if e &&& 1 = 1 then mulMod64 acc b m else acc)

@[inline] partial def gcd64 (a b : UInt64) : UInt64 :=
  if b = 0 then a else gcd64 b (a % b)

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
        y := mulMod64 y y n + c; if y ≥ n then y := y - n
      let mut k : Nat := 0
      while k < r && g = 1 do
        ys := y
        let bound := min 128 (r - k)
        for _ in List.range bound do
          y := mulMod64 y y n + c; if y ≥ n then y := y - n
          q := mulMod64 q (if x ≥ y then x - y else y - x) n
        g := gcd64 q n
        k := k + bound
      r := r * 2
      if r > 4000000 then break
    if g = n then
      g := 1
      while g = 1 do
        ys := mulMod64 ys ys n + c; if ys ≥ n then ys := ys - n
        g := gcd64 (if x ≥ ys then x - ys else ys - x) n
    if g != n && g != 1 then return (some g, rng)
  return (none, rng)

-- ============================================================
-- Dispatch + factorization
-- ============================================================

def smallBound : Nat := 1 <<< 63

def isPrime (n : Nat) : Bool :=
  if n < smallBound then isPrime64 n.toUInt64 else isPrimeGMP n

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
    -- For numbers < 2^63: use unboxed UInt64 rho (blazing fast)
    if m < smallBound then
      let (r, rng') := pollardRho64 m.toUInt64 rng 100
      rng := rng'
      match r with
      | some d => stack := stack.push d.toNat; stack := stack.push (m / d.toNat); continue
      | none => fs := addFactor fs m; continue
    -- For numbers ≥ 2^63: use C FFI (GMP rho + ECM)
    match factorFFI m with
    | some d =>
      if d > 1 && d < m then
        stack := stack.push d; stack := stack.push (m / d)
      else
        fs := addFactor fs m  -- FFI returned degenerate result
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
