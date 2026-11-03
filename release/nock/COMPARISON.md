# Against a native Nock zkVM (M6, analytic)

Zorp's framework (ePrint 2025/1110, *A Framework for Compiling Custom Languages as
Efficiently Verifiable Virtual Machines*) gives a Nock zkVM, `NockVMROM`, as two RAP tables
over the Goldilocks field: a compute table of `N` rows for `N` Nock evaluation nodes and a
memory table of `M + 2L` rows for `M` noun nodes and `L` memory records, 395 field elements of
trace width in all and 175 degree-4 transition gates, at 121 bits of security. The paper reports
no per-program measurements and Nockchain's prover is not a stand-alone command line, so the
comparison here is analytic, from the paper's row accounting against skinock's measured rows.
A live run on the same programs is the paper's M6 proper.

## Rows per Nock step

| | native Nock (Zorp) | Nock in SKI (skinock, measured) |
|---|---|---|
| compute rows per Nock evaluation node | 1 | 2.44–2.48 CPU rows per contraction × 150–270 contractions per Nock step ≈ 370–670 |
| memory rows | `M + 2L`, one per noun node plus two per memory record | one memory cell per loaded or allocated SKI cell: 262,144 for Hoon dec at 12 (33,043 contractions) |
| trace width | 395 elements over Goldilocks (64-bit) | about 140 CPU columns over BabyBear (31-bit), plus memory and program tables |
| transition gates | 175, degree ≤ 4 | 125 CPU constraints, degree ≤ 3 (lean-ski's base circuit) |

So per Nock step skinock spends two to three orders of magnitude more rows, in tables about
three times narrower over a field half the width: roughly 60–100× more trace area per Nock step
than the native design, before jets. Hoon's `++dec` at 12 is 81,895 rows here against an
estimated few hundred compute rows plus memory in NockVMROM.

## What the area buys

- The transition relation is three rules and a spine walk, audited once (`Circuit.export_sound`
  and `export_complete` in lean-ski), against twelve opcodes with a crash discipline the native
  design must specify (Zorp strengthens the Nock specification to make it traversable;
  lean-nock's `Malformed` and `order_*` are the corresponding fixes here, proved).
- Semantics stay outside the circuit: `nockToSki` is a Lean function and the statement is
  recomputed from the formula on the verifier's path; a different Nock, or `+mock`'s scry, is
  a different term, not a different circuit.
- Jets are licensed by theorems (lean-ski's supercombinator jets once for every template, data
  jets by contract), which is M5's transport of lean-nock's three-valued contract; the native
  design licenses jets by convention. With Avon's generic constructor jets the share-mode
  counts above drop about 5.5× (`README.md`), and the loop of `++dec` collapses entirely under
  a transported `dec` jet, which is the number that would close most of the gap on loops.

## Why the live run is not here

Checked 2026-11-04 in `~/Code/zorp/nockchain-official`: the released prover
(`hoon/common/nock-prover.hoon` over `hoon/common/stark/prover.hoon`) takes a
`prover-input` whose versions `%0` and `%1` are the mining puzzle (a block header digest, a
nonce and a proof-of-work length), not a `[subject formula]` pair; the NockVM tables of the
paper live under `hoon/common/v2/table/prover/{compute,memory}.hoon` and are reached only
through that puzzle. Proving the programs here natively would need a Hoon harness that feeds
an arbitrary computation to those tables, plus `hoonc` and the `nockapp` runtime with
`zkvm-jetpack` built from source (`make build-hoonc`). That is a separate engineering task,
the paper's M6 proper, and it is not part of this artifact.

## Caveats

The two row counts are not the same unit: Zorp counts evaluation nodes of the Nock tree, we
count SKI contractions, and the 150–270 ratio between them is the embedding's own cost, which
section 7 of the plan measures per opcode. Widths and fields differ, so "area" is the honest
figure of merit, and it is an estimate until both provers run the same program. The security
levels also differ (121 bits there; lean-ski's released configuration reaches 100 conjectured
bits per round, `ski-air fs-budget`).
