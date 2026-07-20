# Task 4: remove redundant `pock3` fields

## The spec
`pock3 (N, root, m, mode, F)`, elaborated by `parsePock3Spec` into
`pocklington3_certKR (N root m e) (F' : List PrimePow) (mode)`, where `e` is the power of 2 in
`F` (already derived from `F`, not a separate user field). The `pocklington3_certKR` docstring
says outright: *"Inputs (not all needed)."*

## Field-by-field redundancy analysis
Looking at `pocklington3_calculate` (the kernel-checked boolean), each field's role:

- **`N`** — the number to certify. Needed.
- **`root`** — pseudo-primitive root; appears in `powModTR root … N`. A genuine witness.
  Derivable *in principle* by search (the generator tries `a = 2, 3, …`), but it is the core
  Pocklington witness and searching it changes the method's character. **Keep.**
- **`F`** — the factored divisor. Needed (and `e` is read off its leading `2 ^ e`).
- **`mode`** — the non-square certificate. `mode.calculate r s` checks it. The `zero`
  (`s = 0`) and `lt` (`r² < 8s`) cases are decidable from `r, s` alone; only the `prime p`
  (quadratic-non-residue) case needs a witness — and even that is a bounded search. So `mode`
  is *derivable*, but the `prime` case must certify the witness prime and thread it into the
  dict. Non-trivial; **flagged, not done here.**
- **`m`** — the sieve bound. Appears only in the sieve `forallB … m.pred F` and the bound
  `2s + m² < (2F + r)·m + 2`. For a given `F`, the smallest valid `m` is fully determined by
  `r, s` (hence by `N` and `F`). This is exactly what `scripts/prime_cert.py` computes
  (`m = 1; while 2s + m² ≥ (2F+r)m + 2: m += 1`). **`m` is redundant — remove it.**

Every example in the tree passes `m = 1`; none tune it. The elaborator can always compute the
minimal valid `m`.

## Change (this task): drop `m` from the syntax
- New form: `pock3 (N, root, mode, F)`. The elaborator evaluates `F` numerically (via
  `ParsedPrimePow`), computes `R = (N-1)/F`, `r = R mod 2F`, `s = R / 2F`, then the minimal
  `m ≥ 1` with `2s + m² < (2F+r)m + 2`, and passes that `m` to `pocklington3_certKR`.
- A safety cap on the `m` search throws a clear error rather than looping if no valid `m`
  exists (which only happens for an invalid/too-small `F`).

## Back-compat (task 5)
`m` is made **optional** in the syntax rather than deleted: the old
`pock3 (N, root, m, mode, F)` still parses, but emits a deprecation warning and uses the
supplied `m`. New code uses the 4-field form.

## Not done (flagged for review)
- Deriving `mode` automatically (needs QNR witness search + certifying that prime).
- Auto-searching `root`.
Both are larger and change the method's contract, so left for Bhavik to decide.

## Status
`m` made optional + auto-computed, old form deprecated. Framework + a focused test built green.
Existing examples still pass `m` (now deprecated); migrating them is a mechanical follow-up.
