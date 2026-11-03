# The native Nock prover on count-up dec (M6 probe, 2026-11-04)

A bounded attempt to run Zorp's released Nock STARK prover (Nockchain,
`~/Code/zorp/nockchain-official` at `19b0bfdd`, branch
`sigilante/honk-kick-unwind`, 2026-10-31) on the spec's count-up `dec` at 7,
the `countup_dec_7` row of `RESULTS.md`, so that `COMPARISON.md`'s analytic
row accounting has one measured point on the native side. Everything here ran
on the released Hoon prover with its Rust jets, in under 1 GB of memory;
nothing under `~/Code/zorp` was modified (the verifier patches below live in
scratch copies of `hoon/`).

## Summary

| | native NockVM (v2 tables, proof version %5) | skinock (`countup_dec_7`, lean-ski's base circuit) |
|---|--:|--:|
| computation | `[7 F']`, `F'` = count-up dec with opcode 9 desugared (below) | `[7 F]`, the formula as written |
| Nock evaluation nodes | 105 (`F'`); 84 for `F` by the same count | 12,004 SKI contractions |
| compute table rows (raw / padded) | 106 / 128 | 29,591 / 32,768 (CPU table) |
| memory table rows (raw / padded) | 35 / 64 | 262,144 (padded) |
| trace width | compute 11 base + 165 ext + 18 mega-ext; memory 14 + 30 + 24 (262 columns, Goldilocks) | about 140 CPU columns over BabyBear, plus memory and program tables |
| proof size | 74,655 bytes (jam of the `proof` noun, 62 proof-stream objects) | see `results.txt` |
| prove time | about 1.9 s (3.0 s wall for the whole `kick`, of which 1.0 s is loading the 17 MB trap and tracing the computation) | 1.84 s |
| peak RSS, prove | 946 MB (`/usr/bin/time -l`) | 1.32 GB for the whole five-row run |
| verify | rejected: the released memory table covers only computations over a fixed subject (below); the puzzle control verifies | 1.15 s, verified |

The native prover spends about 230× fewer compute rows than skinock on this
program (106 against 29,591) and about 7,500× fewer memory rows (35 against
262,144 padded, though skinock's memory table is padded to the loaded term,
139,919 cells, so about 4,000× on raw cells). This is the measured form of
`COMPARISON.md`'s "two to three orders of magnitude": the rows there were
estimated from the paper's one-row-per-node accounting, and the measurement
confirms it (106 rows for 105 nodes). Per-row cost differs the other way: the
native trace is 262 columns over a 64-bit field against about 140 over a
31-bit field, and the native proof is at 50 bits of security
(`security-level=_50`, `log-expand-factor=_6` in `ztd/eight.hoon:50`) against
skinock's 100 conjectured bits, so the proof-time comparison is not at equal
security.

## What the released prover proves, and the hook

`prove` in `hoon/common/stark/prover.hoon:153` takes `prover-input` (versions
`%0`–`%3`, `%5`: a block-commitment digest, a nonce and `pow-len`), calls
`evaluate-puzzle` (line 137: `puzzle-nock` from `ztd/eight.hoon:897`, which
derives a 64-leaf subject tree from Tip5 of header and nonce and a fixed
`powork` formula of opcodes 0, 1, 3, 6), traces it with `fink:fock`
(`ztd/eight.hoon:616`, the Hoon tracing interpreter, one `formula-data` per
evaluation node), and then calls `generate-proof:prove-door` (line 472) with
`[version header nonce pow-len s f prod return]`. From that point on the
header and nonce only land in the `%puzzle` entry of the proof stream
(`make-proof-work`, line 409); the tables are built from `return` alone
(`build-table-dats return`, line 411). So the door underneath proves an
arbitrary `[s f]`: call `fink:fock [s f]` yourself and hand the result to
`generate-proof` with a dummy header and nonce. That is what the probe does.

The verifier is not symmetric: `verify-inner` (`stark/verifier.hoon:62`)
recomputes `[s f]` from the `%puzzle` entry with `puzzle-nock`, so a proof of
anything but the puzzle fails the stock verifier by construction. The verify
measurements below use a scratch copy of `hoon/` with that one line replaced
by the literal `[s f]`.

## Opcode 9 is not implemented by the tracing interpreter

`fink`'s `interpret` (`ztd/eight.hoon:807–817`) is

```
          [%9 axis=* core=*]    !!
          [%10 [axis=@ value=*] target=*]    !!
          [%11 tag=@ next=*]    !!
```

and the v2 compute table's `%9` is its tag for the cons formula
(`v2/table/prover/compute.hoon:431`, `?^(-.f %9 -.f)`), not Nock 9. The
released NockVM is Nock opcodes 0–8 plus cons. The count-up formula uses 9
twice, and running it as written crashes the interpreter
(`Deterministic(Exit)`, no proof). The paper's constraint tables mention
opcode 9 (`zorp.txt:2089`), so this is a gap of the release against the
paper, not of the design.

The spec's macro `*[a 9 b c] → *[a 7 c 2 [0 1] 0 b]` desugars it exactly, so
the computation proved is

```
F' = [8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 7 [[0 2] [4 0 6] 0 7] 2 [0 1] 0 2] 7 [0 1] 2 [0 1] 0 2]
```

over subject 7, product 6 (`fink` and a reference Nock agree). It has 105
evaluation nodes against 84 for `F` (one 9 node becomes 7, 2, two 0s and the
core's own evaluation), so the 106 rows are about 25% more than the formula
as written would take in a NockVM that implemented 9. The skinock row runs
`F` itself; `nockToSki` handles 9 natively.

## The runs

Toolchain, all prebuilt in the checkout (`target/release/`, 2026-11-03):
`honk` (the Hoon compiler, `crates/tools/honk`; `honk --arbitrary` compiles a
Hoon expression with its `/=` imports to a jammed trap) and `kick` (fires the
trap under honk's evaluation environment, which registers the zkvm-jetpack
prover jets, `crates/tools/honk/src/native/hot.rs:11`). No Rust was built.
Scratch files are in
`/private/tmp/claude-501/-Users-neal-Code-ski/9f357306-0414-4f5c-8eac-a8efa3b89c70/scratchpad/zorp-run/`
(`probe*.hoon`, `memrun.sh` the memory watchdog, `cue.py` to read the output
jams).

| probe | what | honk (compile) | kick (run) | result |
|---|---|---|---|---|
| `triv` | `(add 2 3)` | 2 s | 0.2 s | 5 |
| `z1` | `fink:fock [7 [0 1]]` | 3 s, 643 MB | 0.2 s | 7 |
| `z2` | `fink` on `F` as written | 3 s | crash `Deterministic(Exit)` | opcode 9 |
| `z3` | `fink` on `F'` | 3 s | 0.2 s | product 6, queue of 412 nouns |
| `probe1b` | `F'`: tables built and padded, no proof | 10 s, 2.39 GB | 1.03 s, 889 MB | compute 106→128, memory 35→64 |
| `probe2` | `F'`: full `generate-proof`, version %5 | 9 s, 2.30 GB | 2.96 s, 946 MB | proof, 74,655 bytes, 62 objects |
| `probe1c` | the puzzle itself at `pow-len` 64, tables only | 8 s | 2.06 s | compute 322, memory 577 raw rows |
| `probe2p` | the puzzle at `pow-len` 64, full proof (control) | 10 s, 2.32 GB | 16.5 s, 1.33 GB | proof, 116,895 bytes, 71 objects; heights 512 and 1024 |
| `probe3p` | the puzzle proof through the stock verifier | 10 s | 2.07 s, 926 MB | verified |
| `probe3c` | the `F'` proof through the verifier patched to `[7 F']` | 9 s | 1.03 s | rejected at `linking-checks` (below) |
| `probe2c`/`probe3cc` | `F'` over subject `[7 0]` | 9 s | 3.09 s / 1.03 s | 106 / 36 rows, 74,955 bytes; rejected at the same check |
| `probe2m`, `probe2m2`, `probe3op*` | the one-opcode programs of the verification section | 9–10 s each | 1–3 s each | see that table |

The honk compiles are the expensive step in memory (2.3–2.4 GB RSS to
compile `zeke` plus the prover with the 7.4 MB constraint jams); the prover
run itself stayed under 1 GB. Nothing came near the 3.5 GB ceiling.

For scale, the mining puzzle at the protocol's `pow-len` 64 is 322 compute
rows and 577 memory rows (padded to 512 and 1024), so the count-up program
is a third of one puzzle's compute table.

## Verification: the proof does not verify, and why

The harness is sound: the mining puzzle itself at `pow-len` 64, pushed through
the same probe (`probe2p`: 322 compute and 577 memory rows, padded to 512 and
1024; proof 116,895 bytes, 71 objects; proved in 16.5 s wall at 1.33 GB), is
accepted by the *stock* verifier (`probe3p`, `verify-inner` returns the
`[commitment nonce]` pair; 2.07 s wall, of which about 1 s is loading the
trap). The count-up proof, verified by the verifier with only line 62 patched
to `[7 F']` (`probe3c`), is rejected inside `linking-checks`
(`verifier.hoon:605`), which compares the fingerprints of subject, formula and
product and the two tables' terminal multisets. With the `~&` of each
sub-check turned into a crash label (scratch copy), the failing one is

```
"decode multiset terminal comparison check failed"     (verifier.hoon:681)
```

that is, `%compute-decode-mset` and `%memory-decode-mset` disagree: the
prover's own two tables are inconsistent for this computation (all the
`s`/`f`/`prod` fingerprint checks before it pass). It is not the atom
subject: the same computation over subject `[7 0]` (`[0 7]` → `[0 14]`;
106 compute, 36 memory rows, 74,955 bytes) fails the same check.

One-opcode programs over subject `[7 0]`, each proved and verified with its
own one-line-patched verifier, locate the cause:

| program | opcodes | subject of the inner `[0 2]` | verdict |
|---|---|---|---|
| `[4 0 2]` | 4, 0 | the original | passes linking; fails later in FRI ("last codeword len is not correct", `ztd/six.hoon:197`), a tiny-table edge case at height 4 (64× blowup, fold by 8) |
| `[2 [0 1] [1 0 2]]` | 2, 0, 1 | `*[s [0 1]]` = the original noun | verified |
| `[5 [0 2] [0 2]]` | 5, 0 (a repeated subformula) | the original | verified |
| `[7 [0 1] [0 2]]` | 7, 0 | `*[s [0 1]]` = the original noun | verified |
| `[[2 [0 1] [1 0 2]] 2 [0 1] [1 0 2]]` | cons, 2 (the same formula node evaluated twice) | the original | verified |
| `[7 [1 8 0] [0 2]]` | 7, 1, 0 | `[8 0]`, a new subject | "Nock 0 multiset terminal comparison check failed" (line 686) |
| `[8 [0 2] [0 2]]` | 8, 0 | `[7 [7 0]]`, a new subject | "Nock 0 multiset terminal comparison check failed" |

So the released v2 memory table covers exactly the puzzle's shape. It is
built from one traversal of the initial subject and formula trees
(`rna-bfta ~[[s.return %.y] [f.return %.n]]`,
`v2/table/prover/memory.hoon:407`), and its Nock-0 records come from the
`zeroes` map of the *initial* subject only
(`(~(gut by zeroes.return) -.in ...)`, line 406). Any computation whose
subject changes — opcode 8, or 7 or 2 with a new subject, hence every loop,
since a Nock loop runs its battery against the core as subject — produces
Nock-0 and decode records the memory table does not know, and the compute
table's terminals no longer match it. The puzzle's `powork` is a straight
chain of 6/3/0/1 over a fixed subject and never does this; the paper's
design (`M + 2L` memory rows for `L` memory records across all subjects) is
the general one, and the release's table is the specialization. Count-up
`dec` loops, so its proof cannot verify in the released NockVM. The compute
table, which is the row count `COMPARISON.md` cares about, is unaffected
(one row per evaluation node, 106 here, with the terminal fingerprints of
`s`, `f` and `prod` all checking out); the comparison stands on the compute
rows and on the memory rows the release does emit (35), with the caveat that
a general memory table would be larger.

Verify time for the native proofs that did verify (puzzle, and the small
programs): 1.3–2.1 s wall per `kick`, about 1 s of which is loading the trap,
so roughly 0.3–1 s of verification, unjetted Hoon except for the field and
hash primitives.

## What a proper run would need

The probe is the harness for everything the release can do: `honk
--arbitrary` + `kick` with the prover jets, `fink:fock` on any `[s f]`,
`generate-proof:prove-door` with a dummy puzzle header, and a `/*`-loaded
proof for the verifier. The three missing pieces are in the release, not the
harness. (1) Opcode 9 (and 10, 11) in `fink` and the compute table's op-map,
or the exact desugaring used here (cheap; it costs about 25% more compute
rows on this program). (2) A verifier that takes `[s f]` from the proof
stream instead of recomputing the puzzle: one changed line at
`verifier.hoon:62` plus a proof-stream entry for `[s f]`; the fingerprint
checks at `linking-checks` already bind the tables to `s`, `f` and `prod`.
(3) The real work: a memory table that records Nock-0 fetches and formula
decodes against every subject the computation visits, not only the initial
one (`v2/table/prover/memory.hoon:406–407` and the matching constraints in
`v2/table/verifier/memory.hoon`), which is the paper's `M + 2L` design rather
than the release's single traversal. Without (3) no looping program verifies,
whatever the harness does. (1) and (2) are a day; (3) is a table design with
its soundness argument, weeks, and it would raise the native memory rows
above the 35 measured here. The Rust `nockchain` binary and a Rust build are
not needed for any of it; the Hoon toolchain in `target/release` suffices and
the whole probe stayed under 2.4 GB.

## Reproducing

```
cd ~/Code/zorp/nockchain-official
RUST_LOG=warn target/release/honk --new --arbitrary --output P.jam \
  --prelude hoon/common/hoon.hoon SCRATCH/probe2.hoon hoon
/usr/bin/time -l target/release/kick P.jam P.out.jam
python3 -I SCRATCH/cue.py P.out.jam --depth 4
```

`probe2.hoon` is in the scratch directory above; its text is short enough to
recreate from "The hook" (import `/common/zeke`, `/common/stark/prover`,
`/common/nock-prover`; `fink:fock [s f]`; build `prove-door:prover:np` with
the v2 funcs and `p.pre-2.prep.stark-config`; call `generate-proof` with
`%5`, dummy digests, `pow-len` 64).
