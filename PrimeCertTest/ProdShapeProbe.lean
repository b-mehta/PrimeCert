import Lean

/-! Throwaway: kernel cost of chunk-product shapes over the same synthetic records. -/

namespace ProdShapeProbe

open Lean Elab Command Meta

noncomputable def valK (k : Nat) : Nat := (k.mul 3).succ.add (k.mod 2)

/-- Current shape: balanced tree with a `cnt` cutoff at each leaf. -/
noncomputable def treeK (recs lo cnt d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o => (Nat.blt o cnt).rec 1
      (valK (Nat.add lo (Nat.land (Nat.shiftRight recs (Nat.mul o 16)) 65535))))
    (fun k ih o => Nat.mul (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

/-- Balanced tree, every slot filled. -/
noncomputable def treeFullK (recs lo d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o => valK (Nat.add lo (Nat.land (Nat.shiftRight recs (Nat.mul o 16)) 65535)))
    (fun k ih o => Nat.mul (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

/-- Sequential, by index, small operand first. -/
noncomputable def foldIdxK (recs lo cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1
    (fun n ih => Nat.mul (valK (Nat.add lo (Nat.land (Nat.shiftRight recs (Nat.mul n 16)) 65535))) ih)
    cnt

/-- Sequential, peeling the low record off each step. -/
noncomputable def foldPeelK (recs lo cnt : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 1)
    (fun _ ih r => Nat.mul (valK (Nat.add lo (Nat.land r 65535))) (ih (Nat.shiftRight r 16)))
    cnt recs

/-- Tree whose leaf is four records read from one 64-bit field. -/
noncomputable def tree4K (recs lo d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o =>
      let w := Nat.land (Nat.shiftRight recs (Nat.mul o 64)) 18446744073709551615
      Nat.mul (Nat.mul (valK (Nat.add lo (Nat.land w 65535)))
          (valK (Nat.add lo (Nat.land (Nat.shiftRight w 16) 65535))))
        (Nat.mul (valK (Nat.add lo (Nat.land (Nat.shiftRight w 32) 65535)))
          (valK (Nat.add lo (Nat.shiftRight w 48)))))
    (fun k ih o => Nat.mul (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

/-- Product of the four records in a 64-bit field. -/
noncomputable def quadK (lo w : Nat) : Nat :=
  Nat.mul (Nat.mul (valK (Nat.add lo (Nat.land w 65535)))
      (valK (Nat.add lo (Nat.land (Nat.shiftRight w 16) 65535))))
    (Nat.mul (valK (Nat.add lo (Nat.land (Nat.shiftRight w 32) 65535)))
      (valK (Nat.add lo (Nat.shiftRight w 48))))

/-- Tree whose leaf is eight records read from one 128-bit field. -/
noncomputable def tree8K (recs lo d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o =>
      let w := Nat.land (Nat.shiftRight recs (Nat.mul o 128)) 340282366920938463463374607431768211455
      Nat.mul (quadK lo (Nat.land w 18446744073709551615)) (quadK lo (Nat.shiftRight w 64)))
    (fun k ih o => Nat.mul (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

/-- Tree whose leaf is sixteen records read from one 256-bit field. -/
noncomputable def tree16K (recs lo d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o =>
      let w := Nat.land (Nat.shiftRight recs (Nat.mul o 256))
        115792089237316195423570985008687907853269984665640564039457584007913129639935
      let a := Nat.land w 340282366920938463463374607431768211455
      let b := Nat.shiftRight w 128
      Nat.mul
        (Nat.mul (quadK lo (Nat.land a 18446744073709551615)) (quadK lo (Nat.shiftRight a 64)))
        (Nat.mul (quadK lo (Nat.land b 18446744073709551615)) (quadK lo (Nat.shiftRight b 64))))
    (fun k ih o => Nat.mul (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

/-- Four records of 32 bits each holding `v - base` directly. -/
noncomputable def quadVK (base w : Nat) : Nat :=
  Nat.mul (Nat.mul (Nat.add base (Nat.land w 4294967295))
      (Nat.add base (Nat.land (Nat.shiftRight w 32) 4294967295)))
    (Nat.mul (Nat.add base (Nat.land (Nat.shiftRight w 64) 4294967295))
      (Nat.add base (Nat.shiftRight w 96)))

/-- Tree whose leaf is four direct-value records from one 128-bit field. -/
noncomputable def treeV4K (recs base d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o => quadVK base (Nat.land (Nat.shiftRight recs (Nat.mul o 128))
      340282366920938463463374607431768211455))
    (fun k ih o => Nat.mul (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

/-- `quadK` with `valK` written out. -/
noncomputable def quadIK (lo w : Nat) : Nat :=
  let f := fun x : Nat => let k := Nat.add lo x; Nat.add (Nat.succ (Nat.mul k 3)) (Nat.mod k 2)
  Nat.mul (Nat.mul (f (Nat.land w 65535)) (f (Nat.land (Nat.shiftRight w 16) 65535)))
    (Nat.mul (f (Nat.land (Nat.shiftRight w 32) 65535)) (f (Nat.shiftRight w 48)))

noncomputable def treeI4K (recs lo d off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat)
    (fun o => quadIK lo (Nat.land (Nat.shiftRight recs (Nat.mul o 64)) 18446744073709551615))
    (fun k ih o => Nat.mul (ih o) (ih (Nat.add o (Nat.pow 2 k))))
    d off

meta def valM (k : Nat) : Nat := 3 * k + 1 + k % 2

meta def beqTrue (a b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) a b) (mkConst ``Bool.true)

/-- `probe_shapes variant nChunks seed`: emit one statement per synthetic chunk of 256 records. -/
elab "probe_shapes " v:num n:num s:num : command => liftTermElabM do
  let v := v.getNat
  let mut seed := s.getNat
  let lo0 := 3333333333333333
  let t0 ← IO.monoNanosNow
  for c in [0:n.getNat] do
    -- 256 sorted distinct positions in [0, 65536): one per 256-wide bucket.
    let mut recs := 0
    let mut recsV := 0
    let mut vals : Array Nat := #[]
    for o in [0:256] do
      seed := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      let pos := o * 256 + (seed >>> 56)
      recs := recs ||| (pos <<< (o * 16))
      vals := vals.push (valM (lo0 + c * 65536 + pos))
      recsV := recsV ||| ((valM (lo0 + c * 65536 + pos) - 3 * (lo0 + c * 65536)) <<< (o * 32))
    let pv := vals.foldl (· * ·) 1
    let lo := mkRawNatLit (lo0 + c * 65536)
    let r := mkRawNatLit recs
    let e := match v with
      | 0 => mkAppN (mkConst ``treeK) #[r, lo, mkRawNatLit 256, mkRawNatLit 8, mkRawNatLit 0]
      | 1 => mkAppN (mkConst ``treeFullK) #[r, lo, mkRawNatLit 8, mkRawNatLit 0]
      | 2 => mkAppN (mkConst ``foldIdxK) #[r, lo, mkRawNatLit 256]
      | 3 => mkAppN (mkConst ``foldPeelK) #[r, lo, mkRawNatLit 256]
      | 4 => mkAppN (mkConst ``tree4K) #[r, lo, mkRawNatLit 6, mkRawNatLit 0]
      | 5 => mkAppN (mkConst ``tree8K) #[r, lo, mkRawNatLit 5, mkRawNatLit 0]
      | 6 => mkAppN (mkConst ``tree16K) #[r, lo, mkRawNatLit 4, mkRawNatLit 0]
      | 7 => mkAppN (mkConst ``treeV4K)
          #[mkRawNatLit recsV, mkRawNatLit (3 * (lo0 + c * 65536)), mkRawNatLit 6, mkRawNatLit 0]
      | 8 => mkAppN (mkConst ``treeI4K) #[r, lo, mkRawNatLit 6, mkRawNatLit 0]
      | _ => mkRawNatLit pv
    addDecl <| Declaration.thmDecl
      { name := Name.mkSimple s!"pv{v}_{s.getNat}_{c}", levelParams := []
        type := beqTrue e (mkRawNatLit pv), value := Lean.reflBoolTrue }
  let t1 ← IO.monoNanosNow
  logInfo m!"variant {v}: {n.getNat} chunks, {(t1 - t0) / 1000000} ms"

end ProdShapeProbe

open ProdShapeProbe

probe_shapes 0 400 11
probe_shapes 4 400 11
probe_shapes 7 400 11
probe_shapes 8 400 11
probe_shapes 9 400 11
probe_shapes 9 400 12
probe_shapes 8 400 12
probe_shapes 7 400 12
probe_shapes 4 400 12
probe_shapes 0 400 12
probe_shapes 0 400 13
probe_shapes 4 400 13
probe_shapes 7 400 13
probe_shapes 8 400 13
probe_shapes 9 400 13
