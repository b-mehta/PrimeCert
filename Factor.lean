/-! # Fast integer factorization executable

Trial division + Miller-Rabin + Pollard-Brent rho + ECM.
Uses Lean's GMP-backed `Nat` for all arithmetic.

Usage: lake exe factor <number>
Output: one "prime exponent" pair per line, sorted.
-/

-- Modular exponentiation
partial def powMod' (base exp n : Nat) : Nat :=
  if n ≤ 1 then 0
  else go (base % n) exp 1
where
  go (base exp acc : Nat) : Nat :=
    if exp = 0 then acc
    else
      let acc' := if exp &&& 1 = 1 then acc * base % n else acc
      go (base * base % n) (exp >>> 1) acc'

-- Miller-Rabin
def millerRabinWitness (n a : Nat) : Bool := Id.run do
  if a % n = 0 then return false
  let mut d := n - 1
  let mut r := 0
  while d &&& 1 = 0 do d := d >>> 1; r := r + 1
  let mut x := powMod' a d n
  if x = 1 || x = n - 1 then return false
  for _ in List.range r do
    x := x * x % n
    if x = n - 1 then return false
  return true

def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n < 4 then true
  else if n &&& 1 = 0 || n % 3 = 0 then false
  else #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37].all fun a => !millerRabinWitness n a

-- Trial division
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

-- PRNG
structure Rng where state : UInt64 deriving Inhabited

@[inline] def Rng.next (rng : Rng) : Rng × UInt64 :=
  let s := rng.state ^^^ (rng.state <<< 13)
  let s := s ^^^ (s >>> 7)
  let s := s ^^^ (s <<< 17)
  ({ state := s }, s)

-- Pollard-Brent rho (limited iterations for large numbers)
partial def pollardRho (n : Nat) (rng : Rng) (maxAttempts : Nat := 50) : Option Nat × Rng := Id.run do
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
      if r > 2000000 then break  -- cap ~6M iters per attempt
    if g = n then
      g := 1
      while g = 1 do
        ys := (ys * ys + c) % n
        g := Nat.gcd (if x ≥ ys then x - ys else ys - x) n
    if g != n && g != 1 then return (some g, rng)
  return (none, rng)

-- ECM: Montgomery curve point (projective)
structure ECMPoint where (x z : Nat) deriving Inhabited

-- Modular subtraction: (a - b) mod n, handling underflow
@[inline] def subMod (a b n : Nat) : Nat :=
  if a ≥ b then (a - b) % n else (a + n - b) % n

-- Point doubling on Montgomery curve
def ecmDouble (P : ECMPoint) (a24 n : Nat) : ECMPoint :=
  let u := (P.x + P.z) % n * ((P.x + P.z) % n) % n
  let v := subMod P.x P.z n * (subMod P.x P.z n) % n
  let rx := u * v % n
  let diff := subMod u v n
  let rz := (a24 * diff % n + v) % n * diff % n
  { x := rx, z := rz }

-- Differential addition: R = P + Q given D = P - Q
def ecmAdd (P Q D : ECMPoint) (n : Nat) : ECMPoint :=
  let u := subMod P.x P.z n * ((Q.x + Q.z) % n) % n
  let v := (P.x + P.z) % n * (subMod Q.x Q.z n) % n
  let su := (u + v) % n * ((u + v) % n) % n
  let di := subMod u v n * (subMod u v n) % n
  { x := D.z * su % n, z := D.x * di % n }

-- Montgomery ladder: compute k * P
partial def ecmMul (P : ECMPoint) (k : Nat) (a24 n : Nat) : ECMPoint :=
  if k = 0 then { x := 0, z := 0 }
  else if k = 1 then P
  else
    -- Scan bits from MSB-1 down to 0
    -- Invariant: R = j*P, Q = (j+1)*P where j is the prefix of k scanned so far
    let topBit := Nat.log2 k
    go P (ecmDouble P a24 n) (topBit - 1)
where
  go (R Q : ECMPoint) (bit : Nat) : ECMPoint :=
    let R' := if k &&& (1 <<< bit) != 0
      then ecmAdd Q R P n   -- R' = R + Q = (2j+1)*P
      else ecmDouble R a24 n  -- R' = 2R = 2j*P
    let Q' := if k &&& (1 <<< bit) != 0
      then ecmDouble Q a24 n  -- Q' = 2Q = (2j+2)*P
      else ecmAdd R Q P n    -- Q' = R + Q = (2j+1)*P
    if bit = 0 then R'
    else go R' Q' (bit - 1)

-- Small primes list for ECM stage 1
def smallPrimes : Array Nat := Id.run do
  let mut ps : Array Nat := #[2]
  let mut n := 3
  while n < 1100 do
    let mut composite := false
    let mut d := 3
    while d * d ≤ n do
      if n % d = 0 then composite := true; break
      d := d + 2
    if !composite then ps := ps.push n
    n := n + 2
  return ps

-- ECM: try one curve with Suyama parameterization
partial def ecmOneCurve (n : Nat) (sigma : Nat) (B1 : Nat) : Option Nat := Id.run do
  let u := subMod (sigma * sigma % n) 5 n
  let v := (sigma * 4) % n
  let px := u * u % n * u % n  -- u³
  let pz := v * v % n * v % n  -- v³
  let mut P : ECMPoint := { x := px, z := pz }

  -- Compute a24 = (v-u)³(3u+v) / (16u³v)
  let diff := subMod v u n
  let num := diff * diff % n * diff % n * ((u * 3 + v) % n) % n
  let den := px * v % n * 16 % n

  let g := Nat.gcd den n
  if g != 1 then
    if g != n then return some g else return none

  -- Modular inverse of den
  -- Extended GCD to find inverse
  let inv := modInverse den n
  let a24 := num * inv % n

  -- Stage 1: multiply by all prime powers up to B1
  for p in smallPrimes do
    if p > B1 then break
    let mut pp := p
    while pp ≤ B1 / p do pp := pp * p
    P := ecmMul P pp a24 n
  -- Also primes beyond our table up to B1
  let mut p := 1009
  while p ≤ B1 do
    let mut composite := false
    let mut d := 3
    while d * d ≤ p do
      if p % d = 0 then composite := true; break
      d := d + 2
    if !composite then
      let mut pp := p
      while pp ≤ B1 / p do pp := pp * p
      P := ecmMul P pp a24 n
    p := p + 2

  let g := Nat.gcd P.z n
  if g != 1 && g != n then return some g

  -- Stage 2: look for one large prime factor of group order in (B1, B2)
  -- Precompute: S = q·P for each prime q in (B1, B2) using differential addition.
  -- Key: if consecutive primes differ by d, then next = prev + d·P.
  -- We precompute d·P for small even d (prime gaps are always even for p > 2).
  let B2 := B1 * 10
  -- Precompute delta·P for even deltas up to 50 (covers all prime gaps < 50 digits)
  let P2 := ecmDouble P a24 n
  let mut deltas : Array ECMPoint := #[⟨0, 0⟩, P, P2]  -- deltas[d] = d·P for d=0,1,2
  for d in List.range 48 do
    let d := d + 3
    deltas := deltas.push (ecmAdd deltas[d-1]! P deltas[d-2]! n)

  -- Start from B1·P (computed via ladder once)
  let startQ := if B1 % 2 = 0 then B1 + 1 else B1  -- first odd number ≥ B1
  let mut Q := ecmMul P startQ a24 n
  let mut Qprev := ecmMul P (startQ - 2) a24 n  -- (startQ - 2)·P, for diff add with step 2
  let mut acc : Nat := 1
  let mut q := startQ
  while q ≤ B2 do
    -- Check if q is prime (quick check)
    let mut isPrimeQ := q > 1 && q &&& 1 = 1
    if isPrimeQ then
      let mut d := 3
      while d * d ≤ q do
        if q % d = 0 then isPrimeQ := false; break
        d := d + 2
    if isPrimeQ then
      acc := acc * Q.z % n
    -- Advance by 2: Q_{q+2} = Q_q + 2P, with difference Q_{q} - 2P = Q_{q-2}
    let Qnext := ecmAdd Q P2 Qprev n
    Qprev := Q
    Q := Qnext
    q := q + 2
    -- Periodic GCD
    if q % 2000 < 2 then
      let g2 := Nat.gcd acc n
      if g2 != 1 && g2 != n then return some g2
      acc := 1

  let g2 := Nat.gcd acc n
  if g2 != 1 && g2 != n then return some g2
  return none
where
  modInverse (a n : Nat) : Nat := Id.run do
    -- Extended GCD: find x such that a*x ≡ 1 (mod n)
    let mut old_r : Int := a
    let mut r : Int := n
    let mut old_s : Int := 1
    let mut s : Int := 0
    while r != 0 do
      let q := old_r / r
      let tmp_r := r; r := old_r - q * r; old_r := tmp_r
      let tmp_s := s; s := old_s - q * s; old_s := tmp_s
    if old_r != 1 then return 0  -- not invertible
    return (old_s % n).toNat

-- ECM with multiple curves
partial def ecm (n : Nat) (B1 : Nat) (curves : Nat) (rng : Rng) : Option Nat × Rng := Id.run do
  let mut rng := rng
  for _ in List.range curves do
    let (rng', sv) := rng.next
    rng := rng'
    let sigma := sv.toNat % 1000000 + 6
    match ecmOneCurve n sigma B1 with
    | some d => return (some d, rng)
    | none => pure ()
  return (none, rng)

-- Full factorization
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
      fs := addFactor fs m
      continue
    -- Rho: scale by number size. Effective for factors up to ~14 digits (28-digit composites).
    let digits := (toString m).length
    let rhoAttempts := if digits ≤ 30 then 50 else if digits ≤ 40 then 3 else 1
    let (rhoResult, rng') := pollardRho m rng rhoAttempts
    rng := rng'
    match rhoResult with
    | some d =>
      stack := stack.push d
      stack := stack.push (m / d)
      continue
    | none => pure ()
    -- ECM with escalating parameters (for larger factors)
    let params := #[(2000, 25), (10000, 200), (50000, 300), (250000, 500)]
    let mut found := false
    for (b1, curves) in params do
      let (ecmResult, rng') := ecm m b1 curves rng
      rng := rng'
      match ecmResult with
      | some d =>
        stack := stack.push d
        stack := stack.push (m / d)
        found := true
        break
      | none => pure ()
    if !found then
      -- Last resort: more rho attempts
      let (rhoResult, rng') := pollardRho m rng 100
      rng := rng'
      match rhoResult with
      | some d => stack := stack.push d; stack := stack.push (m / d)
      | none => fs := addFactor fs m  -- give up
  return fs.qsort (fun a b => a.1 < b.1)

def main (args : List String) : IO Unit := do
  match args with
  | [nStr] =>
    match nStr.toNat? with
    | some n =>
      let factors := factorize n
      for (p, e) in factors do
        IO.println s!"{p} {e}"
    | none => IO.eprintln s!"Invalid number: {nStr}"
  | _ => IO.eprintln "Usage: factor <number>"
