# Segmented sieve benchmark matrix

Prepared, not timed. Nothing here has been timed anywhere: every number below is a count or a
size. Compile status per file is in the last section.

Each file holds **one case** — one `run_segment` invocation — so that one measurement per case is
possible. They are under the `PrimeCertTest` lean_lib, which is *not* in `defaultTargets`, so a
bare `lake build` does not touch them; `lake test` does.

Run one case with, for example

    lake env lean -D trace.profiler=true PrimeCertTest/SegBench/B_Off16.lean

and read the `[Kernel]` node of the generated `segEq_*` theorem and its `step_*` lemmas.

`run_segment a W fuel len base?` sieves the window of `W` mod-6 wheel positions starting at the
number `a`, using the base primes at wheel indices `1 … fuel` (so base numbers up to
`value fuel = 3*fuel + 1 + fuel % 2`), in `len`-step batches, against the sieve bitset
`sieveBits_{base}` (default `1000000`).

Every slice below fixes `len = 512` except slice D, which is the `len` sweep itself. That choice
is forced, not tuned: see the note under slice D.

## Baseline rows — subtract these

| file | contents |
| --- | --- |
| `Base0_Startup.lean`  | the imports and nothing else |
| `Base1_Sieve1e8.lean` | `run_sieve 100000000` and no segment |

`Base0` removes import and elaborator startup from every other row. `Base1` is the baseline for
the whole comparison: `E_Base1e8` is `Base1` plus one segment, so `E − Base1` isolates the segment
cost at the base depth that actually certifies primality below `10^16`, and `Base1 − Base0` is the
`10^8` sieve on its own.

## Slice A — window length, offset `10^16 + 1`, base `10^6` (fuel 333333)

| file | W | segment bits |
| --- | --- | --- |
| `A_W256.lean`   | 256   | 256 |
| `A_W1024.lean`  | 1024  | 1024 |
| `A_W4096.lean`  | 4096  | 4096 |
| `A_W16384.lean` | 16384 | 16384 |

## Slice B — offset magnitude, W = 1024, base `10^6` (fuel 333333)

| file | window start | `lo = index a`, bits |
| --- | --- | --- |
| `B_Off12.lean` | `10^12 + 1` | 333333333333, 39 |
| `B_Off14.lean` | `10^14 + 1` | 33333333333333, 45 |
| `B_Off16.lean` | `10^16 + 1` | 3333333333333333, 52 |
| `B_Off18.lean` | `10^18 + 1` | 333333333333333333, 59 |

## Slice C — base depth, offset `10^16 + 1`, W = 1024

| file | fuel | largest base number `value fuel` | base primes scanned |
| --- | --- | --- | --- |
| `C_Fuel3333.lean`   | 3333   | 10000   | 1227 |
| `C_Fuel33333.lean`  | 33333  | 100000  | 9590 |
| `C_Fuel333333.lean` | 333333 | 1000000 | 78496 |

(The prime counts are the base primes at wheel indices `1 … fuel`, i.e. `π(value fuel) − 2`.)

`A_W1024.lean`, `B_Off16.lean` and `C_Fuel333333.lean` are the same case — the shared corner of
the three slices — and carry identical content.

## Slice D — batch length, offset `10^16 + 1`, W = 1024, fuel 333333

| file | len | emitted `step_*` lemmas |
| --- | --- | --- |
| `D_Len128.lean`  | 128  | 2605 |
| `D_Len256.lean`  | 256  | 1303 |
| `B_Off16.lean`   | 512  | 652 |
| `D_Len2048.lean` | 2048 | 163 |

Slice D is the `addDecl` checkpointing tradeoff, and the short end is bounded. The chain proof
term nests one `segLoopK_chain` per batch, and past some nesting depth the kernel rejects the
final theorem with "deep recursion detected". Measured at `fuel = 333333`:

| len | chain links | result |
| --- | --- | --- |
| 16  | 20834 | deep recursion |
| 64  | 5209  | deep recursion |
| 128 | 2605  | accepted |
| 256 | 1303  | accepted |
| 512 | 652   | accepted |

So the ceiling is between 2605 and 5209 links. `len = 128` is therefore the shortest batch in this
slice; a `D_Len64` row existed and was removed because it does not compile. Raising
`maxRecDepth` was not tried — the message names an elaborator option but the failure is on the
kernel side. A balanced chain (halving instead of a left spine) would remove the bound.

## Slice E — the target case, base `10^8`

`E_Base1e8.lean` runs `run_sieve 100000000` first and then a W = 1024 window at `10^16 + 1`
against that base (fuel 33333333). This is the case that would make the survivors *prime* rather
than merely free of small factors, since `(10^8)^2 = 10^16`. **It carries the whole
`SieveVerify1e8` cost before the segment even starts, and it has not been run anywhere.** Treat
its resource needs as unknown and run it alone on a machine with room. `E − Base1` is the segment
cost; `Base1 − Base0` is the sieve cost.

## Naming

Each case sits in its own namespace, `PrimeCert.SegBench.<CaseName>`, and `run_segment` names its
generated declarations inside the namespace it is called from. That matters: the worked-instance
ladder in `PrimeCert.SegmentedSieve` already occupies several of these windows under
`PrimeCert.Sieve`, and a case that repeats one of them would otherwise redeclare the constant.
`run_sieve` is unaffected — it always emits into `PrimeCert.Sieve`, which is what
`run_segment … 100000000` looks up.

## Compile status

Checked with `lake build PrimeCertTest.SegBench.<case>`; CLEAN means the build succeeded with no
error and no warning in its log. These are compile checks only — nothing here was timed.

| file | status |
| --- | --- |
| `Base0_Startup.lean`  | CLEAN |
| `A_W256.lean`         | CLEAN |
| `A_W1024.lean`        | CLEAN |
| `A_W4096.lean`        | CLEAN |
| `A_W16384.lean`       | CLEAN |
| `B_Off12.lean`        | CLEAN |
| `B_Off14.lean`        | CLEAN |
| `B_Off16.lean`        | CLEAN |
| `B_Off18.lean`        | CLEAN |
| `C_Fuel3333.lean`     | CLEAN |
| `C_Fuel33333.lean`    | CLEAN |
| `C_Fuel333333.lean`   | CLEAN |
| `D_Len128.lean`       | CLEAN |
| `D_Len256.lean`       | CLEAN |
| `D_Len2048.lean`      | CLEAN |
| `Base1_Sieve1e8.lean` | UNCHECKED — carries `run_sieve 100000000` |
| `E_Base1e8.lean`      | UNCHECKED — carries `run_sieve 100000000` |

The two unchecked rows are the ones that build the `10^8` sieve, which must not run on the
development box. They are the first thing to try in continuous integration, and the first thing
likely to need adjusting: `E_Base1e8` uses `len = 16384` at `fuel = 33333333`, giving 2035 chain
links, chosen to sit under the 2605 known to be accepted. That keeps it clear of the depth
ceiling at the price of very large individual batches, whose cost here is unmeasured.
