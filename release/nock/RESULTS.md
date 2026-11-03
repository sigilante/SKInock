# release/nock: Nock programs on lean-ski's circuits (M4a, M4b, M4c, M4d, M4f, M4g, M5; 2026-11-04)

Three Nock programs compiled to SKI by `Nock2Ski.compiled` and offered to
lean-ski's base circuit as corpus rows (`ski-air CORPUS OUTDIR`,
`bench/plonky3/src/main.rs`), with no Nock circuit.  `produce.sh` made the
files here; `verify.sh` checks them.  The programs (`programs.txt`: name,
subject, product, form, formula):

| row | program | form | subject | product | contractions | term (cells) |
|---|---|---|--:|--:|--:|--:|
| `countup_dec_7` | the spec's count-up `dec` | `plain` | 7 | 6 | 12,004 | 139,919 |
| `hoon_dec_12` | Hoon's `++dec`, the gate pushed by `[1 …]`, sample 12 | `shared` | 0 | 11 | 33,043 | 60,217 |
| `hoon_dec_0` | the same at sample 0: the underflow crash, `errT` | `shared` | 0 | crash | 4,606 | 60,157 |

A `plain` row is `compiled f s = nockToSki f ⬝ encLit s`; a `shared` row is
`share (compiled f s)` (`Nock2Ski/Share.lean`), the same term with every
subterm of 1,024 cells or more that occurs more than once bound by a λ, so
that ski-air's loader, which shares nothing, writes it once.  The
contraction count is `lake exe nockstatement`'s, lean-ski's `runF` to
weak head normal form, the βs of the sharing included.  It is the count
ski-air's machine checks before it proves a row, and the two agree: on
lean-ski's release row (`release/sumto/sumto_us.term`) `nockstatement
--count-term` prints 10297, the reference in `release/sumto/corpus.txt`.

## The proved rows (`produce.sh`, 2026-11-04)

`ski-air release/nock/corpus.txt release/nock/out` printed (`results.txt`):

```
row               contr   rows budget  memory  prove s verify s  verdict
ik                    1      3     16      16     0.00    0.630  verified
skks                  2      6     16      16     0.02    0.497  verified
countup_dec_7     12004  29591  32768  262144     1.84    1.150  verified
hoon_dec_12       33043  81895 131072  262144     2.42    0.669  verified
hoon_dec_0         4606  11364  16384  131072     0.84    0.674  verified

tampered tables (each proof must be rejected by the verifier):
forged_cell      rejected by the verifier (verify: Lookup(TerminalSumNonZero))
wrong_step       rejected by the verifier (verify: Verification(OodEvaluationMismatch { index: Some(0) )
early_halt       rejected by the verifier (verify: Lookup(TerminalSumNonZero))
forged_loaded    rejected by the verifier (verify: Transcript(LookupPowWitness { bits: 5 }))
```

`ik` and `skks` are ski-air's own first rows; the tampered tables are its
standing forgeries over `skks`.  `rows` is the machine's row count
(contractions and the `App` unwinding steps between them), `budget` the CPU
table's padded height, `memory` the memory table's (the loaded term plus
every cell the run writes, padded; the circuit admits heights to 2^21).
The whole run, rows and proofs, took 19 s and peaked at 1.32 GB
(`/usr/bin/time -l`).

Lean accepted the witness tables ski-air wrote (`lake exe aircheck`,
`Air.checkA`, so `Air.Accepts`):

```
ACCEPT release/nock/out/countup_dec_7.txt (32768 rows, 262144 cells)
ACCEPT release/nock/out/hoon_dec_12.txt (131072 rows, 262144 cells)
ACCEPT release/nock/out/hoon_dec_0.txt (16384 rows, 131072 cells)
```

## Sharing: the Hoon rows before and after (M4b)

In M4a (2026-11-03) the two Hoon rows were refused for their heights:
`encLit` gives every formula-shaped literal its compiled code, and a
battery's nested formulas are encoded once per nesting level, so the term
of Hoon's `%fast`-hinted `++dec` was 2,154,393 cells as a tree, 2.7% over
the 2^21 = 2,097,152 cells the memory and program tables may hold, and
ski-air, which loads a term cell by cell (`build` in `main.rs`), built
2^22-row tables that the verifier refused (`heights [17, 22, 22] out of
bounds`, 5.37 GB peak).  The run itself was small (69,969 and 3,607 machine
rows).

`share` (`Nock2Ski/Share.lean`) binds the repeated subterms with λs, so
each appears once in the prefix text and the heap shares it after the β.
`lake exe nockstatement --cells FORMULA SUBJECT` prints the sizing; at the
release's threshold (`shareMin = 1024` cells):

| row | tree cells | shared cells | bindings | tree contractions | shared contractions | machine rows | rows / contraction |
|---|--:|--:|--:|--:|--:|--:|--:|
| `hoon_dec_12` | 2,154,393 | 60,217 | 28 | 28,324 | 33,043 | 81,895 | 2.478 |
| `hoon_dec_0` | 2,154,333 | 60,157 | 28 | 1,468 | 4,606 | 11,364 | 2.467 |
| `countup_dec_7` (not shared in the release) | 139,919 | 32,549 | 8 | 12,004 | 12,962 | | |

The term is 36 times smaller; the memory tables fell from 2^22 to 2^18 and
2^17.  The βs cost contractions: a bound subterm reaches each use through
an `S`/`K` spine, paid once per copy of the thunk that is forced, so the
proved run of `hoon_dec_12` is 17% longer than the tree's and the short
crash run three times longer.  The threshold is that trade: on
`hoon_dec_12` sharing at 32 cells gives 368,077 cells and 316,721
contractions, at 128 78,849 and 79,002, at 512 58,921 and 35,433, at
1024 60,217 and 33,043, at 4096 80,907 and 30,632, at 131,072 1,474,005
and 28,413 (two bindings).  The count-up row is kept `plain`: it is M4a's
row, unchanged, and it shows both forms proved.

## Hidden subjects: the composed predicate circuit (M4c, 2026-11-04)

Two programs over an atom the prover keeps secret, on lean-ski's composed
predicate circuit (`Ski/Predicate.lean`, `Ski/Circuit/CompPred.lean`), the
statement "I know an atom `n` of 8 bits with `*[n f] = p`" (`hidden/`;
`hidden/programs.txt`: name, subject, product, bits, log CPU height, log
memory height, formula).  The verifier is `nockPredV f 8 = share (λ x ρ.
eqn (nockToSki f (Atom (toBitsT 8 ρ))) x)` (`Nock2Ski/Pred.lean`), the
public `x` is `encNoun p`, and the 8 bits are the circuit's slot cells,
constrained to `K` or `K I` and blinded.  Hoon's `++dec` takes its sample
from the subject (`[8 [1 core] [9 2 [10 [6 [0 3]] [0 2]]]]`).  `lake exe
nockpred` writes the statement and the witness; `ski-air composed-prove`
proved each (lean-ski's `lake exe composed statement` checked the
statement's bytes first); `composed-verify` checks the proof from its
file.

| statement | subject | product | verifier (tree cells) | shared cells | bindings | contractions in the clear | machine rows | memory cells | CPU | memory | prove s | proof bytes | verify s |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| `countup_hidden_7` | 7 (hidden) | 6 | 143,623 | 34,091 | 10 | 17,141 | 42,221 | 84,181 | 2^16 | 2^17 | 5.30 | 762,024 | 0.97 |
| `hoon_dec_hidden_12` | 12 (hidden) | 11 | 2,158,241 | 63,223 | 30 | 41,249 | 101,927 | 183,911 | 2^17 | 2^18 | 10.04 | 817,725 | 0.99 |

`hidden/results.txt` is ski-air's stdout:

```
proved 42221 rows, 84181 memory cells, 1 segments, in 5.30 s; proof 762024 bytes -> release/nock/hidden/countup_hidden_7/countup_hidden_7.proof
proved 101927 rows, 183911 memory cells, 1 segments, in 10.04 s; proof 817725 bytes -> release/nock/hidden/hoon_dec_hidden_12/hoon_dec_hidden_12.proof
```

The hidden stage of `produce.sh` took 22 s and peaked at 1.73 GB.  The
contractions in the clear are `nockpred --run`'s, lean-ski's `runF` on `V
x (boolsT bits)` to `K`; against the base rows (12,004 for count-up `dec`
at 7, 33,043 for Hoon's at 12) the verifier adds the sharing's βs on the
count-up term (it is shared here, 12,962 as a row), the bit conversion
(`toBitsT 8`, 979 cells) and `eqn` on the product.  The machine rows per
contraction are 2.46–2.47, as the base rows'.  The proof is 0.8 MB at
lean-ski's released configuration; `composed-verify` runs Lean's statement
check (about 1 s) and the STARK verifier (under a second).

`verify.sh`, step 4, on each: `nockpred --check` accepts the statement
and refuses it for the product + 1; lean-ski's `composed statement`
accepts the bytes; `composed-verify` accepts the proof and refuses it with
one byte changed (`REJECTED: verify: Verification(InvalidOpeningArgument
…)`).

What an accepted proof says (`Nock2Ski/Pred.lean`, and `README.md`,
"Proofs"): the memory holds 8 bits, of value `n < 256`, with `eqn
(nockToSki f ⬝ encNoun (.atom n)) (encNoun p) ↠ K` (`nock_pred_sound`); so
if Nock evaluates `f` on `n` to any value, that value is `p`
(`nock_pred_sound_val`), and Nock does not crash on `n`
(`nock_pred_sound_crash`).  The converse direction, that Nock terminates on
`n` at all, is the simulation's missing half (`embed_diverges`).  The
statement is complete: `nock_pred_complete` gives the acceptance from
`NockEval (.atom n) f (.val p)` and `n < 2^k`; lean-nock's `countUp_correct
6` is the hypothesis for the first statement, and `HoonOne.dec_correct 11
ctx` with the formula's opcode 8, 10 and 9 steps around the battery for
the second (not composed in Lean here, since `Nock.Fuel` clashes with
`Ski.Basic` as below).  The join to
lean-ski's `Circuit.predExport_sound` is read across the two environments:
`Ski.Predicate` cannot be imported beside lean-nock (both define a
root-level `Outcome`; `Ski/Words.lean:157`, `Nock/Eval.lean:62`).

## Cell-shaped hidden subjects: the public skeleton (M4d, 2026-11-04)

Hoon's compiled `++add` (`urbit/benchmark/desk/bar/add.nock`, the gate's
formula with the subject `[a b]` stripped) over **two** hidden atoms: the
statement "I know atoms `a` and `b` of `k` bits each with `*[[a b] f] =
p`".  The subject is a public **skeleton** with hidden atoms at its leaves
(`Nock2Ski/PredSkel.lean`, `Skel`: `hole w`, `lit n`, `cell l r`), here
`[?k ?k]`; the circuit holds one comb of `N = 2k` bits, `a`'s then `b`'s,
and the verifier

    nockPredS f sk = share (λ x ρ. eqn (nockToSki f (skelT N sk 0 ρ)) x),  skelT [?k ?k] ρ = Cell (Atom (toBitsT k (takeT k ρ))) (Atom (toBitsT k (dropT k ρ)))

cuts the comb with `takeT`/`dropT` (`sliceT N off w`: the whole comb for a
single hole, `dropT off` alone for the last hole, `takeT w` after `dropT
off` otherwise), converts each slice with M4c's `toBitsT`, and rebuilds the
subject with `cellT` and `atomT` (`skel_red`: the result is exactly `encNoun
(sk.fill bs)`).  A one-hole skeleton is M4c's verifier term for term
(`nockPredS_hole`), so `nockpred` takes a skeleton everywhere (`8` is
`?8`) and the M4c files above are unchanged.  Hoon's `add` loops `dec`,
which loops `inc`, so the cost grows with `a` (about `a²/2` inner steps):

| statement | subject | product | bits | verifier (tree cells) | shared cells | bindings | contractions in the clear | machine rows | memory cells | CPU | memory | prove s | proof bytes | verify s | peak RSS |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| `hoon_add_hidden_3_4` | `[3 4]` (hidden) | 7 | 2 × 4 | 11,083,553 | 84,389 | 41 | 38,189 | 94,646 | 197,147 | 2^17 | 2^18 | 10.71 | 823,677 | 1.43 | 1.89 GB |
| `hoon_add_hidden_6_57` | `[6 57]` (hidden) | 63 | 2 × 6 | 11,084,201 | 85,037 | 41 | 91,007 | 225,556 | 352,360 | 2^18 | 2^19 | 20.22 | 878,738 | 1.44 | 3.43 GB |

`hidden/results.txt`'s lines:

```
proved 94646 rows, 197147 memory cells, 1 segments, in 10.71 s; proof 823677 bytes -> release/nock/hidden/hoon_add_hidden_3_4/hoon_add_hidden_3_4.proof
proved 225556 rows, 352360 memory cells, 1 segments, in 20.22 s; proof 878738 bytes -> release/nock/hidden/hoon_add_hidden_6_57/hoon_add_hidden_6_57.proof
```

The tree is 11.1 M cells because `add`'s core carries `dec` and `inc` as
nested batteries, each literal compiled once per nesting level (`encLit`,
M4a's finding); `share` binds the 41 repeated subterms of 1,024 cells or
more and the loaded verifier is 84–85 K cells, 2.6 times the `dec`
statement's.  The skeleton itself costs 1,122 cells around the bits
(`nockpred --cells`).  Rows per contraction are 2.478 on both rows,
memory cells written 2.95 per contraction.  Python's count of the same
program at `[3 4]` is 26,543 contractions (aviary, copy mode); Lean's
38,189 adds the sharing's βs, the two slices and conversions, and `eqn` on
the product.

**What did not fit.**  `[20 30] = 50` at `k = 6` runs in 638,260
contractions in the clear (about 1.58 M rows), over the composed
statement's cap: `ComposedText.logOK` admits heights to 2^20 (ski-air's
`MAX_LOG_HEIGHT` is 21, but a composed statement names its heights and
Lean refuses `log` above 20).  `[12 30] = 42` (262,583 contractions, about
650 K rows and 850 K memory cells) fits 2^20 tables but not this machine's
memory budget.  `[8 30] = 38` (138,008 contractions) was proved at 2^19
and 2^19: 342,149 rows, 489,923 memory cells, 27.4 s, 860,754 bytes,
verified in 1.44 s, but the prover peaked at 5.10 GB, so it is not
released; `[6 57]` at 2^18 and 2^19 (3.43 GB) is the largest `k = 6`
instance under 4 GB.  The hidden stage's lines above are the two released
runs' (13.7 s and 23.2 s wall).

What an accepted proof says (`Nock2Ski/PredSkel.lean`, and `README.md`,
"Cell-shaped hidden subjects"): the memory holds `2k` bits whose halves
are atoms `a, b < 2^k` with `eqn (nockToSki f ⬝ encNoun [a b]) (encNoun p)
↠ K` (`nock_pred2_sound`), so any Nock value of `f` on `[a b]` is `p` and
Nock does not crash on `[a b]`; `nock_pred2_complete` gives the acceptance
from `NockEval [a b] f (.val p)` and `a, b < 2^k`.  Both are instances of
the skeleton theorems `nock_predS_sound` and `nock_predS_complete`, stated
for any skeleton (`sk.ok`: every hole has a bit) over `sk.fill bs`.

## The product as a public value: the probe step (M4f, M4g, 2026-11-04)

The base rows prove evaluation to a weak head normal form; that it encodes
the product is Lean's `embed_outcome`, not a value in the proof.  lean-ski's
probe circuit binds an output by applying the term to marker atoms
constructor by constructor along a public **plan**, the segments of a probe
tree (`Air.planOf`).  Its soundness theorem is generic in the tree
(`Air.air_probe_sound`, `Air.checkPA_sound`); the tree of a SKIlark outcome
(`Probe.toV`) is only its instance.  `Nock2Ski/ProbeTree.lean` gives the
tree `nounV p` of our encoding (`Atom` constructor 0 of 4 with its bits as
the field, `Cell` 1 of 4 with two; bits `Nil | Cons`, 2 markers; bit `T |
F`, 2), proves completeness (`decV_encNoun`) and uniqueness (`encS_unique`,
by determinism of head reduction), and `probe_check`: a table `Air.checkPA`
accepts for `nounPlan p` on a term proves the term's value is `p`
(`ValueIs`); `Nock2Ski/Probe.lean` proves `probe_decodes_nock : ValueIs
(compiled f s) p → NockEval s f (.val p)` (and for `share`) from
`embed_outcome`.  `README.md`, "The product as a public value", has the
chain; the join is read across the two Lean environments through
`Nock2Ski/Value.lean`.

`produce.sh probe` (`probe/`): for each row whose product is a noun, `lake
exe nockprobe plan PRODUCT` writes the plan (`NAME.plan`), `nockprobe jets`
the term's jet file (`NAME.jets`: lean-ski's `JetTable.jetTable` licenses
template roots inside the Nock terms, SKIlark's supercombinator templates
matching generic bracket-abstraction subterms), and Avon runs the segments
(`avon witness --plan`; its plan reader, `src/probe.c`, is generic) and
writes the table with probe segments, released gzipped
(`NAME.probe.table.gz`).  `nockprobe check` runs `Air.checkPA` on it.

| row | product | tree | segments | markers | roots / jets | contractions (plain) | rows | memory cells | padded | check s | table |
|---|--:|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| `countup_dec_7` | 6 | `Atom [F T T]` | 8 | 18 | 9,259 / 24 | 12,099 (+95) | 29,829 | 175,586 | 2^15 × 2^18 | 0.47 | 2.6 MB (691 KB gz) |
| `hoon_dec_12` | 11 | `Atom [T T F T]` | 10 | 22 | 4,146 / 26 | 33,165 (+122) | 82,203 | 157,767 | 2^17 × 2^18 | 1.61 | 4.6 MB (1.0 MB gz) |

The `+n` is the cost of reading the product after the row's run (12,004
and 33,043 contractions): about 12 contractions per probe segment.  With
the jet table instantiated (`avon witness --jet-table --plan`, the same
tables `nockprobe check` also accepts, not released):

| row | contractions | rows | memory cells | instantiations | padded | check s |
|---|--:|--:|--:|--:|--:|--:|
| `countup_dec_7` | 6,279 | 17,760 | 162,567 | 688 | 2^15 × 2^18 | 0.79 |
| `hoon_dec_12` | 18,431 | 52,139 | 125,692 | 1,945 | 2^16 × 2^17 | 0.41 |

`probe/results.txt` is the stage's output:

```
countup_dec_7: product 6: 8 segments, 18 markers; jet file: 9259 roots, 24 jets
countup_dec_7: avon witness --plan: contractions 12099 rows 29829 cells 175586 loaded 139920 insts 0
countup_dec_7: avon witness --jet-table --plan: contractions 6279 rows 17760 cells 162567 loaded 139920 insts 688
ACCEPT release/nock/probe/out/countup_dec_7.probe.jetted.table: the term of countup_dec_7 has the value 6 (32768 rows, 262144 cells, 8 segments, 9259 roots)
ACCEPT release/nock/probe/out/countup_dec_7.probe.table: the term of countup_dec_7 has the value 6 (32768 rows, 262144 cells, 8 segments, 9259 roots)
countup_dec_7: probe-prove-table: proved 32768 rows (0 instantiations, 8 segments), 262144 memory cells, in 2.09 s; proof 609390 bytes -> release/nock/probe/countup_dec_7.probe.proof
countup_dec_7: probe-verify: VERIFIED countup_dec_7: the term decodes to the tree of 6 (8 segments; 1.196 s)
hoon_dec_12: product 11: 10 segments, 22 markers; jet file: 4146 roots, 26 jets
hoon_dec_12: avon witness --plan: contractions 33165 rows 82203 cells 157767 loaded 60218 insts 0
hoon_dec_12: avon witness --jet-table --plan: contractions 18431 rows 52139 cells 125692 loaded 60218 insts 1945
ACCEPT release/nock/probe/out/hoon_dec_12.probe.jetted.table: the term of hoon_dec_12 has the value 11 (65536 rows, 131072 cells, 10 segments, 4146 roots)
ACCEPT release/nock/probe/out/hoon_dec_12.probe.table: the term of hoon_dec_12 has the value 11 (131072 rows, 262144 cells, 10 segments, 4146 roots)
hoon_dec_12: probe-prove-table: proved 131072 rows (0 instantiations, 10 segments), 262144 memory cells, in 3.41 s; proof 598190 bytes -> release/nock/probe/hoon_dec_12.probe.proof
hoon_dec_12: probe-verify: VERIFIED hoon_dec_12: the term decodes to the tree of 11 (10 segments; 0.679 s)
```

**The STARK of the probe table (M4g).**  ski-air's probe prover and
verifier took their plan only from `lake exe jets plan OUTCOME`, a SKIlark
outcome (`err | val n…`, `Probe.toV`).  lean-ski's branch `probe-plan-file`
(commit `a12b13e`, "probe: the output as a literal probe tree") lets the
outcome words name any probe tree: `tree`, then the tree's nodes in
preorder, `c k n` each for `V.node c k ch` with `n = ch.length`
(`Ski/ProbeText.lean`: `Probe.vWords`, `Probe.vOfWords`; plain decimal,
`c < k`, so one tree has one spelling; the same cap of 65,536 segments).
`jets plan`, `jets check-probe` and `circuit compare-probe` take either
form, and ski-air passes the words through to Lean unchanged
(`probe.rs::lean_plan`, `jets.rs::compare_probe`): nothing in the
statement check changed, and every SKIlark outcome form still works
(lean-ski's `release/verify.sh` step 5 passes).  The theorem of the export
path is `Circuit.probeExport_sound_tree`, generic in the tree and
concluding `Probe.DecV t.toO v`; `probeExport_sound` is its instance at
`Probe.toV o`.

`nockprobe tree PRODUCT` writes `nounV p` in that form (`NAME.tree`: 25
and 31 words), `verify.sh` recomputes and compares it, and `ski-air
probe-prove-table TERM JETS TABLE PROOF $(cat NAME.tree)` proves the
released (plain) table, `probe-verify CORPUS probe/ NAME PROOF $(cat
NAME.tree)` checks the proof against the corpus row (`jets
statement-stdin` on the jet file), the plan Lean gives for the tree and
Lean's AIRs (`compare-probe`).  So the accepted proof instantiates
`Circuit.probeExport_sound_tree` at `nounV p`, which with `probe_value`
is `probe_sound`'s conclusion `ValueIs t p`, and `probe_decodes_nock`
makes it `*[s f] = p`, with `p` read from the public tree.

| row | product | tree words | segments | table rows (padded) | memory cells | prove s | peak RSS | proof bytes | verify s |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| `countup_dec_7` | 6 | 25 | 8 | 29,829 (2^15) | 262,144 | 2.09 | 447 MB | 609,390 | 1.20 |
| `hoon_dec_12` | 11 | 31 | 10 | 82,203 (2^17) | 262,144 | 3.41 | 783 MB | 598,190 | 0.68 |

The verify time is `probe-verify`'s own clock, after its three Lean calls
(statement, plan, compare-probe; about 1 s each as `lake exe`).  ski-air's
own run of the segments (`probe-prove`, not released) instantiates the jet
file's roots and reproduces Avon's jetted runs row for row: 17,760 rows
(688 instantiations, 162,567 cells, 2.12 s, 610,894 bytes) and 52,139
(1,945, 125,692 cells, 2^16 rows, 1.78 s, 561,538 bytes); the released
proofs are of the released tables, the ones `nockprobe check` accepts.

Refusals (`verify.sh` step 5): each proof is refused for the tree of the
product + 1 and of the cell `[p 0]` (`verify: Transcript`), with one byte
changed at the middle (`verify: Verification`), and `countup_dec_7`'s
proof offered as `hoon_dec_12`'s is refused before verification (`heights
[15, 18, …] out of bounds`, the term's); for the SKIlark outcome `val 6`
it is refused too (another tree, so another plan).  A truncated tree,
one with `c ≥ k`, a leading zero or words after the tree has no plan
(`plan: NO PLAN FOR tree …`).

`verify.sh`, step 5: Lean recomputes the plan and the tree words from the
product and the jet file from the corpus term and compares them with the
released files, accepts each released table (`ACCEPT …: the term of NAME
has the value p`), refuses it for the product + 1 and for the cell `[p
0]`, and runs the refusals of the proof above.  No Avon is needed to
verify; ski-air is, built from lean-ski's `probe-plan-file` branch.

## Jetted rows: lean-ski's supercombinator jets (M5, 2026-11-04)

No new jet is built here (no Avon C jet, no lean-ski data-jet circuit; the
transported `dec` data jet of `Nock2Ski/JetTransport.lean` is a theorem
without a circuit, held).  These rows use lean-ski's **existing**
supercombinator-jet machinery (`Ski/Inst.lean`, `Ski/JetTable.lean`,
`Ski/AirJet.lean`, `Ski/Circuit/JetSound.lean`): code jets of SKIlark's
compiler templates, generic bracket-abstraction shapes that
`JetTable.jetTable` finds inside the loaded Nock term and licenses as
roots; an instantiation row writes a template's body for its arguments in
one step where the plain run pays the β-chain.  The jet files are the ones
the probe step wrote (`probe/NAME.jets`, `nockprobe jets`): 9,259 roots in
the count-up term, 4,146 in Hoon's `++dec`, 4,139 in the crash row.

`produce.sh jets` (`jets/`): `ski-air jets-measure TERM JETS TABLE` runs the
row with the roots instantiated and writes the jetted witness table
(`NAME.jetted.table.gz`), printing the plain run beside it and proving and
verifying the table in-process; Avon's `witness --jet-table` writes the
same table byte for byte (compared; Avon also prints the contraction
counts); `lake exe nockprobe check-jets` accepts it bound to the row
(lean-ski's `Air.checkJA`); `ski-air jet-prove` writes the proof
(`NAME.jetted.proof`) and `jet-verify` checks it against the corpus row and
the jet file, Lean checking the jet file first (`lake exe jets
statement-stdin`).  `results.txt`:

```
countup_dec_7: jet file: 9259 roots, 24 jets
countup_dec_7: jets-measure: plain 29591 rows, 175296 cells; jetted 17716 rows, 162491 cells, 683 instantiations; padded CPU 32768, POP 4096, INSTW 512
countup_dec_7: jets-measure: jetted: proved in 1.95 s, verified in 1.189 s
countup_dec_7: avon witness --jet-table writes the same table (contractions 6270 rows 17716 cells 162491 loaded 139920 insts 683)
ACCEPT countup_dec_7.jetted.table: a jetted run of the term of countup_dec_7 (32768 rows, 262144 cells, 9259 roots, 24 jets)
countup_dec_7: jet-prove: proved 32768 rows (683 instantiations), 262144 memory cells, in 1.95 s; proof 553128 bytes -> release/nock/jets/countup_dec_7.jetted.proof
countup_dec_7: jet-verify: VERIFIED countup_dec_7: the proof checks against its term and Lean's jet table (1.171 s)
hoon_dec_12: jet file: 4146 roots, 26 jets
hoon_dec_12: jets-measure: plain 81895 rows, 157396 cells; jetted 52084 rows, 125598 cells, 1939 instantiations; padded CPU 65536, POP 8192, INSTW 1024
hoon_dec_12: jets-measure: jetted: proved in 1.43 s, verified in 0.701 s
hoon_dec_12: avon witness --jet-table writes the same table (contractions 18420 rows 52084 cells 125598 loaded 60218 insts 1939)
ACCEPT hoon_dec_12.jetted.table: a jetted run of the term of hoon_dec_12 (65536 rows, 131072 cells, 4146 roots, 26 jets)
hoon_dec_12: jet-prove: proved 65536 rows (1939 instantiations), 131072 memory cells, in 1.43 s; proof 503004 bytes -> release/nock/jets/hoon_dec_12.jetted.proof
hoon_dec_12: jet-verify: VERIFIED hoon_dec_12: the proof checks against its term and Lean's jet table (0.692 s)
hoon_dec_0: jet file: 4139 roots, 26 jets
hoon_dec_0: jets-measure: plain 11364 rows, 74154 cells; jetted 10275 rows, 73079 cells, 164 instantiations; padded CPU 16384, POP 512, INSTW 64
hoon_dec_0: jets-measure: jetted: proved in 0.92 s, verified in 0.701 s
hoon_dec_0: avon witness --jet-table writes the same table (contractions 3960 rows 10275 cells 73079 loaded 60158 insts 164)
ACCEPT hoon_dec_0.jetted.table: a jetted run of the term of hoon_dec_0 (16384 rows, 131072 cells, 4139 roots, 26 jets)
hoon_dec_0: jet-prove: proved 16384 rows (164 instantiations), 131072 memory cells, in 0.92 s; proof 504796 bytes -> release/nock/jets/hoon_dec_0.jetted.proof
hoon_dec_0: jet-verify: VERIFIED hoon_dec_0: the proof checks against its term and Lean's jet table (0.687 s)
```

| row | contractions plain → jetted | machine rows plain → jetted | instantiations | memory cells plain → jetted | CPU / POP / INSTW | prove s | verify s | proof bytes | prover peak |
|---|--:|--:|--:|--:|---|--:|--:|--:|--:|
| `countup_dec_7` | 12,004 → 6,270 (−48%) | 29,591 → 17,716 (−40%) | 683 | 175,296 → 162,491 | 2^15 / 2^12 / 2^9 | 1.95 | 1.17 | 553,128 | 418 MB |
| `hoon_dec_12` | 33,043 → 18,420 (−44%) | 81,895 → 52,084 (−36%) | 1,939 | 157,396 → 125,598 | 2^16 / 2^13 / 2^10 | 1.43 | 0.69 | 503,004 | 325 MB |
| `hoon_dec_0` | 4,606 → 3,960 (−14%) | 11,364 → 10,275 (−10%) | 164 | 74,154 → 73,079 | 2^14 / 2^9 / 2^6 | 0.92 | 0.69 | 504,796 | 199 MB |

The plain rows are the base circuit's (`results.txt` above: 29,591, 81,895,
11,364).  `rows` are the CPU table's before padding (contractions, `App`
unwinding steps and instantiation rows); POP and INSTW are the two side
tables of the jet circuit (the arguments popped and the cells written per
instantiation), padded.  The jetted runs match the probe step's jetted
measurements (M4f, `avon witness --jet-table --plan`: 17,760 rows and 688
instantiations, 52,139 and 1,945, the probe segments adding 44 and 55 rows
and 5 and 6 instantiations).  The whole stage took 21 s and peaked at
418 MB.

**What the fall means.**  The templates are generic: they collapse the
β-chains of bracket abstraction that the compiler writes everywhere (the
`force` continuations, the `pull`s, the Scott-case λs), so about half the
contractions and 36–40% of the rows go on the two public rows, and 10% on
the crash row, which is mostly the sharing's βs before the underflow.  The
`dec` loop itself is paid in full: each iteration's contractions remain,
and the rows stay proportional to the count (count-up `dec` at 7 is seven
iterations; at 70 the jetted rows would be about ten times these).  What
would collapse the loop to a constant is the transported **data** jet,
`cw .dec` as one row (`jet_transport`, README "Jet transport"), whose
circuit is not built.  PLAN §3.2: the transported jet licenses a value and
says nothing about steps; this table is the measurement that limitation
asks for, with the jets that exist.

**What an accepted jetted proof says** (README, "Jet transport"):
`Circuit.jetExport_sound` (lean-ski) for the row's term, `rootsOKB` checked
by `jets statement`, gives `Air.AcceptsJ` and, by `Air.air_sound_jet`, a
final weak head normal form `v` with `∃ v', Eval t v' ∧ WSteps v' v`
(`Mach.jet_run_eval`) and `∃ v', Eval t v' ∧ chead v' = chead v`
(`jet_run_shape`); `embed_outcome` on `Eval t v'` (through
`compiled_terminates`/`shared_terminates`) makes `v'` an encoding of Nock's
product or `Err` for its crash, so `v` has that head.  `nockprobe
check-jets`'s `ACCEPT` is `Air.checkJA_sound`, the same `AcceptsJ` from the
table itself.

Refusals (`verify.sh` step 6): each table is refused bound to another row
(`REJECT …: its term is not the term of NAME`); each proof is refused
offered as another row's (`heights […] out of bounds`, the term's) and with
one byte changed at the middle (`verify: Verification(…)`).  A tampered
table (one row's counter changed) is refused by `check-jets` (`not a jetted
run of NAME with its jet table`).

## Rows per contraction

| row | contractions | machine rows | rows / contraction |
|---|--:|--:|--:|
| `sumto_us` (lean-ski's release) | 10,297 | 25,074 | 2.435 |
| `countup_dec_7` | 12,004 | 29,591 | 2.465 |
| `hoon_dec_12` (shared) | 33,043 | 81,895 | 2.478 |
| `hoon_dec_0` (shared) | 4,606 | 11,364 | 2.467 |
| `hoon_dec_12` (tree, M4a, refused) | 28,324 | 69,969 | 2.470 |
| `hoon_dec_0` (tree, M4a, refused) | 1,468 | 3,607 | 2.457 |

The Nock rows match sumto's ratio.

## What an accepted proof says

`README.md`, "Proofs", has the chain of theorems; in short, for a `shared`
row: `Circuit.export_sound` (lean-ski) gives `Eval (share (compiled f s))
v` for the proof's final state `v`; `shared_value` (`Nock2Ski/Share.lean`,
from `compiled_value` and `share_red`) gives `WSteps (share (compiled f
s)) ep` for an encoding `ep` of Nock's product, `Enc p ep`, under
lean-nock's `NockEval s f (.val p)` (`HoonOne.dec_correct`); `enc_whnf`
says `ep` is a weak head normal form, and `eval_back` with
`Eval.deterministic` identify the two: `WSteps v ep` (`shared_value_eval`).
For the crash row, `shared_crash_eval : WSteps v errT` under
`HoonOne.dec_underflow`.  For the `plain` row, `compiled_value_eval` with
`countUp_correct`.

## What the files are

- `programs.txt`: the statements, name, subject, product, form (`plain` or
  `shared`), formula.  The formula and subject are the public input; the
  term is recomputed from them.
- `corpus.txt`: the rows `nockstatement` wrote, `NAME COUNT PREFIXTERM`,
  ski-air's input.  `verify.sh` recomputes each with `nockstatement
  --check` and trusts no term from the file.
- `results.txt`: ski-air's stdout for `corpus.txt`, quoted above.
- `hidden/programs.txt`, `hidden/NAME/public.txt`, `hidden/NAME/NAME.proof`,
  `hidden/results.txt` (M4c, M4d): the hidden-subject statements (name,
  subject, product, skeleton, log CPU height, log memory height, formula),
  their proofs (the composed path writes and verifies a proof file) and
  ski-air's lines.  The skeleton column is public: `8` is one hidden atom
  of 8 bits, `[?4 ?4]` a cell of two hidden atoms of 4 bits each.  The
  witness (the subject's bits) is written to a temporary directory and
  never under `release/`; `programs.txt` records the subject so that
  `produce.sh` reproduces the run.
- `probe/NAME.plan`, `probe/NAME.tree`, `probe/NAME.jets`,
  `probe/NAME.probe.table.gz`, `probe/NAME.probe.proof`,
  `probe/results.txt` (M4f, M4g): the probe plan of the product (`nockprobe
  plan`, `Air.planOf (nounV p) 0`), the tree itself as the outcome words
  ski-air takes (`nockprobe tree`: `tree`, then `nounV p`'s nodes in
  preorder), the term's jet file (`nockprobe jets`, lean-ski's `jetTable`),
  the table with probe segments Avon wrote for the plan (`avon witness
  --plan`, gzipped; `probe/out/`, not committed, holds it unpacked and the
  jetted run), ski-air's proof of that table (`probe-prove-table`, verified
  by `probe-verify` against the corpus row, the jet file and the tree), and
  the stage's output.  `nockprobe check` accepts the table for the row and
  the product (`Air.checkPA`, `probe_check`, `probe_decodes_nock`); the
  proof needs ski-air from lean-ski's `probe-plan-file` branch (above).
- `jets/NAME.jets`, `jets/NAME.jetted.table.gz`, `jets/NAME.jetted.proof`,
  `jets/results.txt` (M5): the row's jet file (`nockprobe jets`, lean-ski's
  `jetTable` over `allTemplates`; the same as `probe/NAME.jets`), the jetted
  witness table ski-air's `jets-measure` wrote with the licensed roots
  instantiated (Avon's `witness --jet-table` writes the same bytes;
  gzipped), its proof (`ski-air jet-prove`, verified by `jet-verify` against
  the corpus row and the jet file, Lean's `jets statement-stdin` first), and
  the stage's output.  `nockprobe check-jets` accepts the table for the row
  (`Air.checkJA`, so `Air.checkJA_sound`, `Air.air_sound_jet`;
  `embed_outcome` reads the final state).  No Avon is needed to verify.
- `out/` (not committed; `produce.sh` and `verify.sh` regenerate it):
  `NAME.txt`, the witness table of each row in Lean's format, the file
  `aircheck` accepts.  **There are no proof files.**  ski-air's base path
  (`ski-air CORPUS OUTDIR`) proves each row and verifies the proof in the
  same process (`prove_and_verify`), the verifier recomputing the circuit
  from the public term and checking it against Lean's `Circuit.baseAirs`
  (`lake exe circuit compare`, the hypothesis of `Circuit.export_sound`);
  the proof is never serialized, and there is no verify-only entry point
  for base proofs (those exist for the jetted, probe and composed paths).
  So `verify.sh` re-proves: its ski-air run is prove-and-verify, and it
  checks that the run reports the recorded rows, contractions, machine
  rows, budget and memory.
