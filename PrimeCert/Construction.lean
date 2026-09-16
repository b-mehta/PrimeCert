/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import PrimeCert.Pocklington3

/-! Bounded, untrusted certificate construction. Every emitted ladder is checked by the kernel. -/
public section
namespace PrimeCert.Construction

/-- The opt-in search policy; all work is finite. Bounds are inclusive. -/
structure Budget where
  maxBits : Nat := 512
  maxDepth : Nat := 32
  maxAttempts : Nat := 1024
  factorFuel : Nat := 1024
  trialBound : Nat := 9999
  smoothBounds : List Nat := [64, 512, 4096, 32768, 262144, 524288]
  smoothBases : List Nat := [2, 3]
  rhoRestarts : Nat := 2
  rhoSteps : Nat := 32768
  witnessBases : List Nat := [2, 3, 5, 7, 11, 13, 17]
  randomWitnesses : Nat := 32
  maxFactors : Nat := 12
  maxSubsets : Nat := 4096
  maxSieveBound : Nat := 64
  seed : UInt64 := 17
  deriving Repr, Inhabited

inductive Mode where
  | pock | zero | lt | interval (w : Nat)
  deriving Repr, BEq, Inhabited

structure Node where
  n : Nat
  root : Nat
  mode : Mode
  factors : List (Nat × Nat)
  sieveBound : Nat := 1
  deriving Repr, BEq, Inhabited

structure State where
  attempts : Nat := 0
  seed : UInt64 := 17
  nodes : Array Node := #[]
  leaves : Array Nat := #[]
  -- Try each child once per remaining depth; failed alternatives share that result.
  failed : Array (Nat × Nat) := #[]
  deriving Repr, BEq, Inhabited

/-- No-factor and whole-modulus outcomes are distinct; neither is a proper factor. -/
inductive SmoothResult where
  | noFactor | whole | factor (d : Nat)
  deriving Repr, BEq, Inhabited

/-- Stage-one Pollard p−1. `primes` must be strictly ascending and cover every prime
through `bound`.
The tactic reads these from PrimeCert's existing certified sieve cache. -/
def pMinusOne (primes : Array Nat) (n base bound : Nat) : SmoothResult := Id.run do
  if n < 4 || base ≤ 1 || n ≤ base then return .noFactor
  let initial := Nat.gcd base n
  if 1 < initial then
    return if initial < n then .factor initial else .whole
  let mut x := base % n
  for q in primes do
    if q > bound then break
    let mut power := q
    for _ in [:bound.log2 + 1] do
      if power ≤ bound / q then power := power * q else break
    x := powMod x power n
  let g := Nat.gcd ((x + n - 1) % n) n
  return if g == 1 then .noFactor else if g < n then .factor g else .whole

private def probablePrime (n : Nat) : Bool := Id.run do
  if n < 2 then return false
  if n == 2 then return true
  if n % 2 == 0 then return false
  let mut d := n - 1
  let mut s := 0
  for _ in [:n.log2 + 1] do
    if d % 2 != 0 then break
    d := d / 2
    s := s + 1
  for a in [2, 3, 5, 7, 11, 13, 17] do
    if a ≥ n then continue
    let mut x := powMod a d n
    if x == 1 || x == n - 1 then continue
    let mut passed := false
    for _ in [:s - 1] do
      x := x * x % n
      if x == n - 1 then passed := true; break
    if !passed then return false
  return true

private def spend (budget : Budget) : StateM State Bool := do
  let st ← get
  if st.attempts ≥ budget.maxAttempts then return false
  set { st with attempts := st.attempts + 1 }
  return true

private def draw : StateM State Nat := do
  let st ← get
  let seed := st.seed * 6364136223846793005 + 1442695040888963407
  set { st with seed }
  return seed.toNat

private def proper (n d : Nat) : Bool := 1 < d && d < n && n % d == 0

private def splitFactor (budget : Budget) (primes : Array Nat) (n : Nat) :
    StateM State (Option Nat) := do
  for bound in budget.smoothBounds do
    for base in budget.smoothBases do
      unless ← spend budget do return none
      if let .factor d := pMinusOne primes n base bound then
        if proper n d then return some d
  for _ in [:budget.rhoRestarts] do
    unless ← spend budget do return none
    let c := (← draw) % (n - 1) + 1
    let mut x := (← draw) % (n - 2) + 2
    let mut y := x
    for _ in [:budget.rhoSteps] do
      x := (x * x + c) % n
      y := (y * y + c) % n
      y := (y * y + c) % n
      let d := Nat.gcd (max x y - min x y) n
      if proper n d then return some d
      if d == n then break
  return none

private def insert (q e : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(q, e)]
  | (p, k) :: rest => if p == q then (p, k + e) :: rest else (p, k) :: insert q e rest

/-- Partial factor data, validated before subset selection or child certification. -/
structure Factors where
  factors : List (Nat × Nat)
  residual : Nat
  deriving Repr, Inhabited

private def trial (budget : Budget) (primes : Array Nat) (n : Nat) : Factors := Id.run do
  let mut m := n
  let mut factors := []
  for q in primes do
    if q > budget.trialBound then break
    let mut e := 0
    for _ in [:n.log2 + 1] do
      if m == 0 || m % q != 0 then break
      m := m / q
      e := e + 1
    if e != 0 then factors := (q, e) :: factors
  return ⟨factors, m⟩

/-- Default finite factor provider. Unresolved components remain in `residual`. -/
def factor (budget : Budget) (primes : Array Nat) (n : Nat) : StateM State Factors := do
  let initial := trial budget primes n
  let mut factors := initial.factors
  let mut stack := [initial.residual]
  let mut residual := 1
  for _ in [:budget.factorFuel] do
    match stack with
    | [] => break
    | m :: rest =>
      stack := rest
      if m ≤ 1 then continue
      if probablePrime m then factors := insert m 1 factors; continue
      if let some d ← splitFactor budget primes m then
        stack := d :: m / d :: stack
      else residual := residual * m
  return ⟨factors, stack.foldl (· * ·) residual⟩

/-- Validate sizes before exponentiation, then the exact partial-factor product. -/
def validate (n : Nat) (data : Factors) (maxFactors : Nat) : Bool := Id.run do
  if n < 2 || data.factors.length > maxFactors || data.residual == 0 then return false
  let mut product := data.residual
  let mut seen := []
  for (q, e) in data.factors do
    if q < 2 || q ≥ n || e == 0 || e > n.log2 || seen.contains q then return false
    seen := q :: seen
    for _ in [:e] do
      if product > (n - 1) / q then return false
      product := product * q
  return product == n - 1

private def product (fs : List (Nat × Nat)) : Nat :=
  fs.foldl (fun f (q, e) => f * q ^ e) 1

private structure Criterion where
  mode : Mode
  sieveBound : Nat := 1
  deriving BEq

private def criterion (budget : Budget) (n f : Nat) : Option Criterion := Id.run do
  if n < f * f then return some ⟨.pock, 1⟩
  if f % 2 != 0 || (n - 1) / f % 2 != 1 then return none
  let r := (n - 1) / f % (2 * f)
  let s := (n - 1) / f / (2 * f)
  let m := minimalSieveBound (2 * f) r s
  if m == 0 || m > budget.maxSieveBound then return none
  for l in [1:m] do
    if n % (l * f + 1) == 0 then return none
  if s == 0 then return some ⟨.zero, m⟩
  if r * r < 8 * s then return some ⟨.lt, m⟩
  let d := r * r - 8 * s
  let w := d.sqrt
  if w * w < d && d < (w + 1) * (w + 1) then return some ⟨.interval w, m⟩
  return none

private def childCost (budget : Budget) (primes : Array Nat) (q : Nat) : Nat :=
  if primes.contains q then 0 else
    let data := trial budget primes (q - 1)
    if (criterion budget q (product data.factors)).isSome then 1 else 2 + q.log2 / 32

private def choices (budget : Budget) (primes : Array Nat) (n : Nat)
    (data : Factors) : List (List (Nat × Nat) × Criterion) := Id.run do
  if !validate n data budget.maxFactors then return []
  let factors := data.factors.mergeSort (fun x y => x.1 ≤ y.1)
  let costs := factors.map fun (q, _) => childCost budget primes q
  let count := 2 ^ factors.length
  let mut selected := []
  for i in [:min count budget.maxSubsets] do
    let mask := if count ≤ budget.maxSubsets then i else if i == 0 then count - 1 else i - 1
    let fs := factors.zipIdx.filterMap fun (f, j) => if mask.testBit j then some f else none
    if let some mode := criterion budget n (product fs) then
      let cost := costs.zipIdx.foldl
        (fun s (c, j) => if mask.testBit j then s + (16 * c + 1) * (n.log2 + 1) else s)
        (mode.sieveBound - 1)
      selected := (cost, fs, mode) :: selected
  return (selected.mergeSort (fun x y => x.1 ≤ y.1)).map Prod.snd

private def witness (budget : Budget) (n : Nat) (fs : List (Nat × Nat)) :
    StateM State (Option Nat) := do
  for i in [:budget.witnessBases.length + budget.randomWitnesses] do
    unless ← spend budget do return none
    let a ← if let some a := budget.witnessBases[i]? then pure a
      else do pure ((← draw) % (n - 2) + 2)
    if powMod a (n - 1) n != 1 then continue
    if fs.all (fun (q, _) => Nat.gcd (powMod a ((n - 1) / q) n - 1) n == 1) then
      return some a
  return none

private def generate (budget : Budget) (primes : Array Nat) : Nat → Nat → StateM State Bool
  | 0, _ => pure false
  | depth + 1, n => do
    if n.log2 + 1 > budget.maxBits then return false
    if (← get).nodes.any (·.n == n) || (← get).leaves.contains n then return true
    if primes.contains n then
      modify fun st => { st with leaves := st.leaves.push n }
      return true
    if (← get).failed.contains (n, depth + 1) then return false
    if !probablePrime n then return false
    -- Try table factors before spending smooth/rho work. Failed candidates are not retried.
    let mut tried := []
    for phase in [:2] do
      let data ← if phase == 0 then pure (trial budget primes (n - 1))
        else factor budget primes (n - 1)
      for (fs, choice) in choices budget primes n data do
        if tried.contains (fs, choice) then continue
        tried := (fs, choice) :: tried
        let some root ← witness budget n fs | continue
        let mut success := true
        for (q, _) in fs do
          if !(← generate budget primes depth q) then success := false; break
        if !success then continue
        let node := ⟨n, root, choice.mode, fs, choice.sieveBound⟩
        modify fun st => { st with nodes := st.nodes.push node }
        return true
    modify fun st => { st with failed := st.failed.push (n, depth + 1) }
    return false

/-- Construction outcome, including consumed work and advanced deterministic seed on exhaustion.
This is untrusted search data, not a primality theorem. -/
def run (budget : Budget) (primes : Array Nat) (n : Nat) : Bool × State :=
  (generate budget primes budget.maxDepth n).run { seed := budget.seed }

end PrimeCert.Construction
