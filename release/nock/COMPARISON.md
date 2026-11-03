# Against a native Nock zkVM (M6, analytic)

Zorp's framework (ePrint 2025/1110, *A Framework for Compiling Custom Languages as
Efficiently Verifiable Virtual Machines*) gives a Nock zkVM, `NockVMROM`, as two RAP tables
over the Goldilocks field: a compute table of `N` rows for `N` Nock evaluation nodes and a
memory table of `M + 2L` rows for `M` noun nodes and `L` memory records, 395 field elements of
trace width in all and 175 degree-4 transition gates, at 121 bits of security. The paper reports
no per-program measurements and Nockchain's prover is not a stand-alone command line, so the
comparison here is analytic, from the paper's row accounting against skinock's measured rows.
`ZORP-RUN.md` adds one measured native point (count-up `dec` at 7 on the released prover,
section "The live run" below); a live run on all three programs with a verifying memory table is
the paper's M6 proper.

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

## The live run (`ZORP-RUN.md`)

Checked 2026-11-04 in `~/Code/zorp/nockchain-official`: the released prover
(`hoon/common/nock-prover.hoon` over `hoon/common/stark/prover.hoon`) takes a
`prover-input` that is the mining puzzle (a block header digest, a nonce and a proof-of-work
length), not a `[subject formula]` pair, but the door underneath it
(`generate-proof:prove-door`) proves whatever `fink:fock` traced, so a short Hoon probe
compiled with the checkout's `honk` and fired with `kick` runs the native prover on count-up
`dec` at 7. `ZORP-RUN.md` has the run. The measured native rows for that program are 106
compute rows (one per evaluation node; 105 nodes once opcode 9, which the released
interpreter does not implement, is desugared by the spec's macro) and 35 memory rows,
padded to 128 and 64, a 74,655-byte proof in about 1.9 s at 946 MB, against 29,591 and
262,144 rows here. That is the measured form of the two-to-three orders of magnitude
estimated above: 230× on compute rows. Two caveats from the run: the native proof is at 50
bits of security (`security-level=_50`) against 100 here, and it does not verify, because
the released memory table only records fetches against the initial subject (every loop
changes the subject); the puzzle itself, pushed through the same harness, verifies. That is
the release's known scope, the mining-puzzle subset: opcode 9 and the general memory table
are Zorp's pending zkVM work, so the measurement is of a partial release. The
analytic comparison above stands as the comparison of designs; the measured compute rows
confirm its native side.

## Caveats

The two row counts are not the same unit: Zorp counts evaluation nodes of the Nock tree, we
count SKI contractions, and the 150–270 ratio between them is the embedding's own cost, which
section 7 of the plan measures per opcode. Widths and fields differ, so "area" is the honest
figure of merit, and it is an estimate until both provers run the same program. The security
levels also differ (121 bits there; lean-ski's released configuration reaches 100 conjectured
bits per round, `ski-air fs-budget`).
