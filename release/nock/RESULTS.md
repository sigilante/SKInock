# release/nock: Nock programs on lean-ski's base circuit (M4a, 2026-11-03)

Three Nock programs compiled to SKI by `Nock2Ski.compiled` and offered to
lean-ski's base circuit as corpus rows (`ski-air CORPUS OUTDIR`,
`bench/plonky3/src/main.rs`), with no Nock circuit.  `produce.sh` made the
files here; `verify.sh` checks them.  The programs (`programs.txt`: name,
subject, product, budget, formula):

| row | program | subject | product | contractions | term (cells) |
|---|---|--:|--:|--:|--:|
| `countup_dec_7` | the spec's count-up `dec` | 7 | 6 | 12,004 | 139,919 |
| `hoon_dec_12` | Hoon's `++dec`, the gate pushed by `[1 …]`, sample 12 | 0 | 11 | 28,324 | 2,154,393 |
| `hoon_dec_0` | the same at sample 0: the underflow crash, `errT` | 0 | crash | 1,468 | 2,154,333 |

The contraction count is `lake exe nockstatement`'s, lean-ski's `runF` to
weak head normal form.  It is the count ski-air's machine checks before it
proves a row, and the two agree: on lean-ski's release row
(`release/sumto/sumto_us.term`) `nockstatement --count-term` prints 10297,
the reference in `release/sumto/corpus.txt`.

## The proved row (`produce.sh`, 2026-11-03)

`ski-air release/nock/corpus.txt release/nock/out` printed (`results.txt`):

```
row               contr   rows budget  memory  prove s verify s  verdict
ik                    1      3     16      16     0.00    0.489  verified
skks                  2      6     16      16     0.02    0.488  verified
countup_dec_7     12004  29591  32768  262144     1.81    1.157  verified

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

Lean accepted the witness table ski-air wrote (`lake exe aircheck`,
`Air.checkA`, so `Air.Accepts`):
`ACCEPT release/nock/out/countup_dec_7.txt (32768 rows, 262144 cells)`.

## The rows over the budget

ski-air loads a term cell by cell with no sharing (`build` in `main.rs`), and
the compiled `++dec` is 2,154,393 cells: 2.7% over the 2^21 = 2,097,152
cells the memory and program tables may hold.  The run itself is small
(69,969 and 3,607 machine rows, CPU heights 2^17 and 2^12); the term is
what overflows.  Over the three-row corpus, the same command printed, for
these two rows, exactly

```
hoon_dec_12: FAILED an honest table: heights [17, 22, 22] out of bounds
hoon_dec_0: FAILED an honest table: heights [12, 22, 22] out of bounds

2 FAILURES
```

(the heights are the CPU, memory and program tables' log2; the prover built
the 2^22-row tables and the verifier refused them, `MAX_LOG_HEIGHT = 21`),
and exited 1.  That run peaked at 5.37 GB (`/usr/bin/time -l`), so the two
rows sit in `over.txt` and the `over` stage of `produce.sh` and `OVER=1` of
`verify.sh` are off by default; both demand that each row is refused for
its heights and for no other reason.  The count check passed for all three
rows: ski-air reports `N contractions, reference M` when it does not, and
it did not.

The size is the compiler's, not the program's: `encLit` gives every
formula-shaped literal its compiled code, and a battery's nested formulas
are encoded once per nesting level, so Hoon's `%fast`-hinted `++dec`
battery costs 2.15 M cells where the Python compiler's hash-consed DAG of
the same program is about 6,000 nodes.  Sharing the code of nested
literals in `nockToSki`/`encLit` (or a loader that shares) would bring the
rows within budget by a factor of about 300; it changes the pinned terms,
so it is M4 work, not M4a.

## Rows per contraction

| row | contractions | machine rows | rows / contraction |
|---|--:|--:|--:|
| `sumto_us` (lean-ski's release) | 10,297 | 25,074 | 2.435 |
| `countup_dec_7` | 12,004 | 29,591 | 2.465 |
| `hoon_dec_12` | 28,324 | 69,969 | 2.470 |
| `hoon_dec_0` | 1,468 | 3,607 | 2.457 |

The Nock rows match sumto's ratio; the unpadded row counts of the two
over-budget rows are read from the tables ski-air wrote (the padding
repeats the halt row).

## What the files are

- `programs.txt`: the statements, name, subject, product, budget (`base`
  or `over`), formula.  The formula and subject are the public input; the
  term is recomputed from them.
- `corpus.txt`, `over.txt`: the rows `nockstatement` wrote, `NAME COUNT
  PREFIXTERM`, ski-air's input.  `verify.sh` recomputes each with
  `nockstatement --check` and trusts neither file's term.
- `results.txt`: ski-air's stdout for `corpus.txt`, quoted above.
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
