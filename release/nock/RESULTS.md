# release/nock: Nock programs on lean-ski's circuits (M4a, M4b, M4c, M4d, M4f; 2026-11-04)

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

## The product as a public value: the probe step (M4f, 2026-11-04)

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
hoon_dec_12: product 11: 10 segments, 22 markers; jet file: 4146 roots, 26 jets
hoon_dec_12: avon witness --plan: contractions 33165 rows 82203 cells 157767 loaded 60218 insts 0
hoon_dec_12: avon witness --jet-table --plan: contractions 18431 rows 52139 cells 125692 loaded 60218 insts 1945
ACCEPT release/nock/probe/out/hoon_dec_12.probe.jetted.table: the term of hoon_dec_12 has the value 11 (65536 rows, 131072 cells, 10 segments, 4146 roots)
ACCEPT release/nock/probe/out/hoon_dec_12.probe.table: the term of hoon_dec_12 has the value 11 (131072 rows, 262144 cells, 10 segments, 4146 roots)
```

`verify.sh`, step 5: Lean recomputes the plan from the product and the jet
file from the corpus term and compares them with the released files,
accepts each released table (`ACCEPT …: the term of NAME has the value p`),
and refuses it for the product + 1 and for the cell `[p 0]`.  No Avon is
needed to verify.

**What waits on lean-ski: the STARK proof of the probe table.**  ski-air's
`probe-prove`, `probe-prove-table` and `probe-verify` take their plan only
from `lake exe jets plan OUTCOME` (`bench/plonky3/src/probe.rs:101`,
`lean_plan`), and `bench/Jets.lean:256-278` (`parseOutcome`,
`planOfOutcome`) knows only SKIlark outcomes, `err | val n…`, through
`Probe.toV` (`Ski/ProbeTree.lean:201`); `compare_probe`
(`bench/plonky3/src/jets.rs:922`) has `lake exe circuit compare-probe`
recompute the plan from the outcome the same way (`bench/Circuit.lean:
309-365`).  A jets directory is required and its file must be exactly the
term's jet file (`jets statement-stdin`), so a zero-root file would be
refused: the files here are the ones to use.  The AIRs and the theorems
are generic in the plan; what needs generalising is the plan's input
(`jets plan` taking a tree or a plan file, `compare-probe` taking the plan,
`lean_plan` reading a file).  Then `ski-air probe-prove TERM JETS TABLE
PROOF` on `probe/NAME.plan` is the proof whose statement
`probe_sound`/`probe_decodes_nock` give.

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
- `probe/NAME.plan`, `probe/NAME.jets`, `probe/NAME.probe.table.gz`,
  `probe/results.txt` (M4f): the probe plan of the product (`nockprobe
  plan`, `Air.planOf (nounV p) 0`), the term's jet file (`nockprobe jets`,
  lean-ski's `jetTable`), the table with probe segments Avon wrote for the
  plan (`avon witness --plan`, gzipped; `probe/out/`, not committed, holds
  it unpacked and the jetted run), and the stage's output.  `nockprobe
  check` accepts the table for the row and the product (`Air.checkPA`,
  `probe_check`, `probe_decodes_nock`).  There is no proof file: ski-air's
  probe prover takes a plan only from a SKIlark outcome (above).
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
