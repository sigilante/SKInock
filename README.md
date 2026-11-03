# skinock

Nock in SKI, with its jets. A compiler from Nock 4K formulas to closed SKI terms, built
on [SKIjack](https://github.com/sigilante/SKIjack), checked against
[urbit/benchmark](../../urbit/benchmark)'s reference tests and Hoon-compiled programs on
aviary-kernel and on [Avon](https://github.com/sigilante/avon); and a Lean development
joining [lean-nock](https://github.com/sigilante/lean-nock) (Nock 4K, the three-valued jet
contract, co-derivation) to [lean-ski](https://github.com/sigilante/lean-ski) (SKI, the
heap machine, licensed jets, the circuit). `PLAN.md` is the plan; this file is what exists.

## The compiler (`python/skinock`)

```
pip install -e python
python -m skinock run "[4 0 1]" 41                 # 42 (271 contractions)
python -m skinock run FORMULA SUBJECT --avon       # on Avon, share mode (--copy, --discover)
python -m skinock run FORMULA SUBJECT --interp     # literals without code: nockI interprets
python -m skinock compile FORMULA SUBJECT --out p.dag   # Avon's dag form (--text, --source)
python -m skinock nock FORMULA SUBJECT             # the Python reference evaluator
python -m skinock check                            # urbit/benchmark norm/tests.json: 63/63 agree
python -m skinock bench dec add                    # Hoon-compiled programs at scaled subjects
```

```python
from skinock import nock as N
from skinock.run import Program
p = Program(N.parse("[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]"),
            N.parse("5"))        # the spec's count-up decrement
p.run().value                    # 4
```

**Nouns** are a Scott sum `Atom bits | Cell h t | Form h t code | Err` (`nock.ski`): an atom
is its bits least significant first, a cell a pair, `Form` a cell that parses as a formula
and carries its compiled code, `Err` a crash. **Formulas** compile to SKIjack expressions
over a subject variable (`compile.py`), one combinator of the runtime library per opcode:
projections for 0, the literal for 1, `app` for 2, `cel` for 3, `inc` for 4, `eq` for 5,
`ifn` for 6, and `force` wherever Nock evaluates an operand before using it. A literal
cell that parses as a formula is emitted as `Form` with its code, so a battery pushed by
`[1 …]` has live arms and opcode 9 pulls one by axis and applies it: this is SKIjack's door
convention, and it is why Hoon's compiled output runs without an interpreter.

**Strictness is Nock's.** Both halves of an autocons, both operands of 2, 5 and 10, the
pushed value of 8, the subject of 7 and 9 and the hint of a dynamic 11 are forced (one
case on the noun, which also propagates `Err`) before use, in the order lean-nock
discharged against Vere: head before tail, subject before formula. The branches of 6 are
left unevaluated until chosen. A forced value is deep: every field is a value, so a crash
cannot hide in an unread position and the three outcomes value, crash and divergence
coincide with Nock's. A node's shape is checked before its operands run, as lean-nock's
`Malformed` does, so `[6 c 99]` crashes even when `c` would diverge.

**Products** are read behaviourally (`run.py`): the term is applied to one marker atom per
constructor and reduced to weak head normal form, recursively; on Avon (`avon.py`) a show
term over free atoms rebuilds the noun as a first-order term and the normal form is parsed.
A dynamic formula built from data (a plain `Cell` reaching opcode 2 or 9) goes to the
interpreter fallback `nockI s f` in `nock.ski`: a Nock 4K evaluator over the noun sum,
opcodes 0–11 and autocons, with the same strictness and order as the compiled code,
dispatching on the opcode's bits and walking dynamic axes from the most significant bit.
A `Form` met in formula position runs its code, so `Form` keeps its fast path.
`Program(f, s, code=False)` encodes every literal as a plain `Cell`, which forces the
interpreter and is how the tests re-run the reference suite through it. `nockI` is the
file's only recursive equation: the helpers (`nockP`, `nockO`, `autocons`, `appI`, …) take
the evaluator as a parameter `ev`, so that lean-ski's front end, which ties self-recursion
but not mutual recursion, compiles the file to the same terms as skijack (M3).

**Opcode 12** is lean-nock's crash by default (Vere outside `+mock`): the compiler supplies
`op12 ev s t = Err`, the crash before the operands, as `malformed` has it. As an extension,
`Program(f, s, scry=[((ref, path), value), …])` compiles a resolver `scry x p` over the fact
table, compared structurally, and `[12 ref path]` (compiled, or `op12` in the interpreter)
evaluates both operands then consults it; a miss is a crash. The Python evaluator takes the
same table as `resolver=`.

`nock.py` is the reference: a parser and printer for `[a b c]` notation, `is_formula`, and
an evaluator in Vere's order that counts steps, the oracle `check.py` and `bench.py`
compare against.

## Measurements (2026-11-03)

urbit/benchmark's Hoon-compiled programs at scaled subjects, products checked against the
Python evaluator. Contractions are aviary's (copy mode, arguments shared but reductions
not); Avon's share mode (Turner graph reduction) is about two thirds of that.

| program | subject | product | Nock steps | contractions | per step | DAG nodes |
|---|---|---|--:|--:|--:|--:|
| dec | 5 / 20 / 100 | 4 / 19 / 99 | 72 / 222 / 1,022 | 14,116 / 52,600 / 278,710 | 196 / 237 / 273 | 6,050 |
| add | [3 4] / [20 30] | 7 / 50 | 167 / 2,683 | 29,147 / 604,817 | 175 / 225 | 8,991 |
| factorial | 3 / 5 | 6 / 120 | 829 / 34,189 | 155,170 / 7,857,983 | 187 / 230 | 19,779 |
| fibonacci | 5 / 8 | 5 / 21 | 1,127 / 7,955 | 203,302 / 1,524,933 | 180 / 192 | 22,635 |
| ackermann | [1 2] / [2 2] | 4 / 7 | 215 / 1,191 | 32,693 / 191,907 | 152 / 161 | 16,113 |
| bigslot | 0 | 0 | 53,233 | 14,037,181 | 264 | |

Avon, share mode, from the `dag` input form (70–260 KB where the printed form is 12–158 MB):
dec 100 in 170,041, dec 1000 in 1,684,702, factorial 5 in 5,088,741, fibonacci 8 in
1,017,378, bigslot in 8,741,269 contractions, each in well under a second, all with the right
product. Avon's generic constructor and data jets (`--discover --data`, no new code) cut
those by about 5.5× (dec 1000: 304,807). Larger subjects, Avon share mode: dec 10,000 in
16.8 M contractions (0.3 s, 168 per Nock step), add 300 + 400 in 76.5 M (1.3 s, 166 per step),
fibonacci 12 in 20.0 M (146 per step), ackermann (2, 3) in 232,576 (111 per step); every
product is the oracle's. The interpreter fallback
(`nockI`, formulas as data) costs about 8× the compiled code on the same programs.

## Against a native Nock zkVM

`release/nock/COMPARISON.md`: an analytic comparison with Zorp's NockVMROM from its paper's row
accounting (one compute row per Nock node, two tables, 395-wide over Goldilocks) against the rows
measured here (about 2.45 rows per contraction, 150–270 contractions per Nock step): two to three
orders of magnitude more rows per Nock step in narrower tables, roughly 60–100× the trace area
before jets, bought with a three-rule circuit audited once, semantics outside the circuit, and
jets licensed by theorems. A live run of the same programs on both provers is future work.

## The Lean package

`lakefile.toml` requires lean-ski and lean-nock by path; lean-nock must be on its
`lean-4.31` branch (four small edits for Lean 4.31.0, its gates passing).
`scripts/lean-check.sh` builds and prints axioms.

- `Nock2Ski/Noun.lean`: the encodings. `bitsT` is lean-ski's `BitArith.bl`, `encNoun` the
  four-constructor Scott sum as bracket abstraction leaves it, with eliminator lemmas.
- `Nock2Ski/Decls.lean` (M3): `nock.ski` as bytes plus `op12 ev s t = Err`, its parse by
  lean-ski's front end written out as `nockDecls`, and `parse_pin : Front.parseFile nockSrc =
  some nockDecls` by `decide +kernel`; `nockFile` (the bytes compiled) equals `nockFileD`
  (the declarations compiled), so no later pin parses the file in the kernel.
- `Nock2Ski/Prims.lean`: the eleven M1 primitives of `nock.ski` compiled by lean-ski's own
  SKIjack front end (`parseFile` then `compileDecls`; `compileFile` refuses the file because
  its object-type pass mistakes `noun` for an object type, and that refusal is itself a
  theorem) and pinned by `decide +kernel` to the terms the Python compiler emits
  (`terms/*.ski`, identical character for character). Specs proved for all of them:
  `hd_spec`, `tl_spec`, `cel_spec` (lean-nock's `wut`), `force_spec`, `inc_spec` with the
  crash on a cell, `eq_spec` and `eq_tisN` (lean-nock's `tisN`), `ifn_*`, and
  `pull_tagged` for axis pulls. Axioms: `propext`, `Quot.sound`, and `Classical.choice` where
  `omega` enters; no `sorry`, no `native_decide`.
- `Nock2Ski/InterpDefs.lean` … `Nock2Ski/Interp.lean` (M3): the interpreter fallback,
  pinned. Every equation of `nock.ski` from `decop` to `app` (22 of them, and the 14
  constructors of `op`) is defined as the file's term and pinned to `Front.termOf nockFile`
  (`x_pin`); its structure, as skijack lifts the λs (each λ-chain its own closed combinator
  over the binders it captures, `nockOK5`, …), is kernel-checked (`x_eq`, `InterpEq.lean`,
  `InterpEqI.lean`), so that the kernel evaluates each term's chain of dependencies once,
  shared between the two sides; the terms equal Python's character for character. β for
  every combinator (`absN_beta_close` through `absNF`, the closing by propositional
  rewrites, since unfolding `OTerm.close` definitionally makes the kernel evaluate every
  constant in the term), `nockO` on each opcode tag (`nockO_O2`, …), and the pure specs:
  `decop_spec` (an opcode's canonical bits to its tag, `Obad` from 13 on, by kernel runs),
  `path_spec` (`revb`, `tlb`: an axis's bits to `axisPath`), `descend_spec` (the `hd`/`tl`
  chain, lazily), `slotB_pos`, `app_cell : app (Cell h t) x ↠ nockI x (Cell h t)`, `app_form`.
  The kernel-heavy theorems are spread over a chain of modules so that each `lean` process
  stays within about 4 GB (`decide +kernel` retains memory across theorems in one process).
- `Nock2Ski/InterpEnc.lean` (M3): the interpreter over `Enc`: the dispatch (`nockI_cell`,
  `nockI_form`, `nockP_atom`, `appI_cell`, `cel2_enc`), `interp_op` (a plain cell `[k t]`
  with `k ≤ 12` is `nockO` on the tag; `k ≥ 13` crashes), `slotB_enc`/`slotB_none` (Nock's
  `/` at a dynamic axis, through `fasO_axisPath`), `editP_enc`/`editB_enc` (Nock's `#`,
  through `haxO_axisPath`), the twins of the compiled `pick_enc` and `editT_enc`.
- `Nock2Ski/Compile.lean` (M2): `nockToSki : Noun → Term`, the compiler, mirroring
  `compile.py`'s `formula` over autocons and opcodes 0–11 (12 and malformed shapes are
  `Err`; `nockToSki_malformed`, with `malformed = Malformed` against lean-nock); the λs
  `compile.py` writes are bracket abstraction (`absN`) over closed subterms; `encLit` is
  `lit`, a `Form` with its compiled code on every formula-shaped literal; `axisPath`, the
  digits of an axis, equals `Front.axisSteps`. One deliberate difference: opcode 10 forces
  the tree before the patch, lean-nock's (and Vere's) order; `compile.py` and `nock.py`
  do the patch first, which differs only in a crash-versus-divergence race.
- `Nock2Ski/Enc.lean` (M2): `Enc n e`, the encoding relation: an atom as `encNoun`, a cell
  as `Cell` of encodings or as `Form` of them with its own code `nockToSki n`. `encNoun n`
  (no code, the hidden subject) and `encLit n` (the runtime's literal) are both `Enc n`.
  Every M1 spec restated over `Enc` (`force_enc`, `eq_enc`, `app_enc`, …; five more `eqn`
  runs for the `Form` combinations), lean-nock's `fasO` and `haxO` as walks along
  `axisPath` (`fasO_axisPath`, `haxO_axisPath`), and the tagged pull over `Enc` (`pick_enc`).
- `Nock2Ski/Embed.lean` (M2, M3): the simulation, one induction on `NockEval` over all
  constructors for the compiled term and the interpreter together (`embed_both`): the two
  are mutual through `app`, since compiled opcode 2 or 9 on a plain `Cell` calls `nockI`
  and `nockI` on a `Form` runs its compiled code, which is the compiled statement at the
  same derivation node; so each case proves the compiled half (M2's proof, `app_sim` now
  using the interpreter's hypothesis on a `Cell`) and derives the interpreter half from it
  on a `Form` and from `interp_op` and the branch lemmas on a `Cell`.
  `embed_crash : NockEval s f .exit → Enc s es → nockToSki f ⬝ es ↠ Err`;
  `embed_value : NockEval s f (.val p) → Enc s es → ∃ ep, Enc p ep ∧ nockToSki f ⬝ es ↠ ep`
  (M2's `Err` disjunct is gone: M3's `app` falls back to `nockI`);
  `nockI_crash : NockEval s f .exit → Enc s es → Enc f ef → nockI ⬝ es ⬝ ef ↠ Err`;
  `nockI_value : NockEval s f (.val p) → Enc s es → Enc f ef → ∃ ep, Enc p ep ∧ nockI ⬝ es
  ⬝ ef ↠ ep`; `compiled_value`, `embed_value_encNoun` likewise strong, and
  `interpreted_value` for the formula as code-free data under `[2 [0 2] [0 3]]`. So the SKI
  term computes exactly Nock's value and crashes exactly where Nock crashes, on all of
  Nock 4K, compiled or interpreted. `compiled f s = nockToSki f ⬝ encLit s`. Axioms as M1;
  no `sorry`.
- `Nock2Ski/Share.lean` (M4b): sharing in the term. `share : Term → Term` hash-conses the
  term into its DAG, binds every node of `shareMin = 1024` cells or more with two or more
  parent edges (the subterms the tree writes more than once), smallest first, and returns
  the let chain `(λx₁. (λx₂. … (λxₙ. C) Lₙ') …) L₁'` by bracket abstraction (`absO`), each
  body `Lⱼ'` its node with its maximal bound subterms as the earlier variables and `C` the
  root's; so the prefix tree is the DAG's size and the heap shares each bound subterm after
  its β. `share_red : share t ↠ t` (`WSteps`), one `abs_beta_close` per binding
  (`chain_red`), the substituted result literally `t`: `shareWith` checks `C.close σ = t`
  (decidable) before it returns the chain, so the hash-consing is outside the trusted
  path. `shared_value : NockEval s f (.val p) → ∃ ep, Enc p ep ∧ share (compiled f s) ↠ ep`
  and `shared_crash` by `WSteps.trans share_red`. Also `enc_whnf : Enc p ep → Whnf ep`,
  `eval_enc`, and the rows' statements `shared_value_eval`, `shared_crash_eval`,
  `compiled_value_eval`, `compiled_crash_eval` (below, "Proofs"). Python's hash-consing of
  literals and formula bodies (`compile.py`) is the DAG analogue of `share`: it names each
  repeated subterm once as a definition, and Avon's `dag` input form carries that sharing,
  where the printed term and ski-air's loader unfold it. The threshold is the sweep
  `nockstatement --cells` prints: a binding costs an `S`/`K` spine in cells and the same
  steps in contractions once per copy of the thunk that is forced, so on Hoon's `++dec`
  (2,154,393 cells, 28,324 contractions as a tree) sharing at 32 gives 368,077 cells and
  316,721 contractions, at 512 58,921 and 35,433, at 1024 60,217 and 33,043, at 4096
  80,907 and 30,632.
- `Nock2Ski/NounText.lean`: the `[a b c]` parser and printer the exes share.
- `bench/NormCheck.lean`, `lake exe normcheck`: the 63 reference tests and the M2 programs
  (the spec's count-up `dec`, Hoon's `++dec` on a gate in the subject and on one pushed by
  `[1 …]`) through `nockToSki`, read back by probing at fresh variables, against the
  reference results and a small evaluator in lean-nock's order: 63/63 and 6/6; and (M3) the
  63 tests again with the formula as code-free data beside the subject, run by
  `[2 [0 2] [0 3]]`, so that the interpreter does the work: 63/63. Both gates in
  `scripts/lean-check.sh`. Hoon's `dec 5` is 11,664 head contractions (aviary measured
  14,116 with the read-out, copy mode); interpreted, the reference tests cost about ten
  times their compiled runs (test 0, `[[4 0 1] [0 1]]` on 42: 181 head contractions
  compiled, 2,294 interpreted).
- `Nock2Ski/Pred.lean` (M4c): the predicate statement over a hidden atom. `bitsK k n`, the
  `k` low bits of `n`; `trim`, the trailing `false`s stripped, with `trim_bits : trim l =
  bits (val l)` (canonical bits are `bits` of their value, `bits_val_canon`); `consTrimT`
  and `toBitsT k`, the closed terms converting the circuit's `k` bits (lean-ski's `boolsT`:
  a `pairT` chain of Scott Booleans, the last alone) to the runtime's canonical `bitsT`,
  with `toBitsT_red : toBitsT k ⬝ boolsT bs ↠ bitsT (trim bs)` for `bs` of length `k`;
  the verifier `nockPredV f k = share (λ x ρ. eqn (nockToSki f (Atom (toBitsT k ρ))) x)`
  by bracket abstraction, `nockPredV_beta`; `nock_pred_complete`, `nock_pred_sound`,
  `nock_pred_sound_val`, `nock_pred_sound_crash` and `eqn_err : eqn Err b ↠ F` (below,
  "Proofs"). `boolsT` is a copy of lean-ski's `CompM.boolsT`: `Ski.Predicate` and
  `Ski.Circuit.CompPred` cannot be imported beside lean-nock, since `Ski.Composed` reaches
  `Ski.Words`, whose root-level `inductive Outcome` (`Ski/Words.lean:157`) clashes with
  lean-nock's (`Nock/Eval.lean:62`); likewise `Nock.Fuel`'s `Diverges` with `Ski.Basic`'s,
  so `Nock.Comp` (`countUp_correct`) is not imported either.
- `Nock2Ski/PredText.lean` (M4c): the statement's text for `nockpred`, copies of lean-ski's
  `combBT`, `encO`, `predStmt`, `addStmts`, `cHeap`, `publicTextC` (the predicate case),
  `cellText`, `logOK`, `privateOK` over lean-ski's own `slotHeap`, `pbuild` and `build`,
  for the same reason; the rendering is checked against the originals at every use, since
  ski-air pipes the statement's bytes to lean-ski's `lake exe composed statement -` before
  it proves or verifies.
- `Nock2Ski/Head.lean` (M4e): counted head reduction `StepsN` and the head length `HLen`
  (lean-ski's `Ski/Converse.lean` lemmas `StepsN.wtail`, `StepsN.app_left`, copied), the
  symbolic head reducer `hred` over open terms with `hred_stepsN`, the checks `pendCheck`,
  `contCheck` with their soundness, and the primitives' head reductions
  (`hlen_force_pend`, `hlen_force_enc`, `hlen_cel_pend`, `hlen_inc_pend`, `hlen_ifn_*`,
  `hlen_eqn_pend`) by `decide +kernel`.
- `Nock2Ski/Pending.lean` (M4e): `Pending n s f`, a `NockEval` derivation cut off after `n`
  costed steps, and `pending_of_noOut`: a run with no outcome is pending at every `n`.
  Over `Nock.Eval` alone (no `Nock.Fuel`).
- `Nock2Ski/Converse.lean` (M4e): `pending_both`, `embed_terminates`, `nockI_terminates`,
  `embed_outcome`, `embed_complete`, `embed_diverges`, `compiled_terminates`,
  `shared_terminates`, `nock_of_eqn_K`, `nock_pred_sound_nock`, `nock_predS_sound_nock`,
  `nock_pred2_sound_nock` (below, "Proofs").
- `bench/NockPred.lean`, `lake exe nockpred` (M4c): `nockpred [--log R M] NAME FORMULA
  PRODUCT K` prints the predicate statement `predicate (nockPredV f K) (encNoun p) K` over
  a one-cell region at CPU and memory heights `2^R` and `2^M`, in the format `ski-air
  composed-prove PUBLIC WITNESS PROOF` and `composed-verify PUBLIC PROOF` consume;
  `--witness NAME SUBJECT K` prints the `K` bits of the atom and the region; `--check NAME
  FORMULA PRODUCT K < public.txt` recomputes the verifier from the formula and compares
  (the statement's verifier, `x`, bit count, region, heights, and the whole text), exit 1
  otherwise, the verifier's Lean check as `skilark statement` is lean-ski's; `--run NAME
  FORMULA PRODUCT SUBJECT K` runs the verifier on the bits in the clear with `runF` and
  reports the contractions and whether it reaches `K`; `--cells FORMULA K` the sizes.
- `bench/NockStatement.lean`, `lake exe nockstatement` (M4a, M4b): `nockstatement NAME
  FORMULA SUBJECT` prints the corpus row ski-air reads, `NAME COUNT PREFIXTERM`, for
  `share (compiled f s)` (`--unshared`: `compiled f s`): the term in lean-ski's prefix form
  (a backtick for application) and its head contractions to weak head normal form by
  lean-ski's `runF`, the βs of the sharing included, the count ski-air's machine checks
  before it proves a row (`--count-term` on lean-ski's `release/sumto/sumto_us.term` prints
  its reference 10297). `nockstatement --check [--unshared] NAME FORMULA SUBJECT <
  corpus.txt` recomputes the row from the formula and compares it with the named row on
  stdin, count and term, exit 1 on a mismatch: the verifier's Lean half, which trusts no
  term from a file. `nockstatement --cells FORMULA SUBJECT [MINSIZE…]` prints the cells,
  depth, bindings and contractions of the term unshared and shared at each threshold, the
  check to run before ski-air (its tables hold 2^21 cells). `scripts/lean-check.sh` runs
  the first two as its M4a/M4b gate.

## Proofs (`release/nock/`, M4a, M4b, M4c, M4d, M4e)

Three Nock programs proved on lean-ski's circuit, with no Nock circuit, as corpus rows of
lean-ski's base circuit (`ski-air CORPUS OUTDIR`): the spec's count-up `dec` at subject 7,
product 6 (`countup_dec_7`: 12,004 contractions, 29,591 machine rows, CPU height 2^15,
memory 2^18); Hoon's `++dec`, the gate pushed by `[1 …]`, at sample 12, product 11
(`hoon_dec_12`: 33,043 contractions, 81,895 rows, CPU 2^17, memory 2^18); and the same at
sample 0, the underflow crash, product `errT` (`hoon_dec_0`: 4,606 contractions, 11,364
rows, CPU 2^14, memory 2^17). Each proved in 0.8–2.4 s and verified in 0.7–1.2 s; the
whole run peaked at 1.32 GB. The Hoon rows are `share (compiled f s)`: as a tree,
`compiled f s` is 2,154,393 cells, 2.7% over the memory table's 2^21, since `encLit`
encodes a battery's nested formula literals once per nesting level and ski-air loads a
term without sharing (M4a's refusal, `heights [17, 22, 22] out of bounds`); `share` binds
the 28 repeated subterms of 1,024 cells or more with λs, 60,217 cells, and the βs add 17%
to the run (3× on the short crash run). `release/nock/RESULTS.md` has ski-air's output,
the before/after table, the threshold sweep and the rows-per-contraction ratios
(2.47–2.48, sumto's 2.435). `release/nock/produce.sh` makes the release and `verify.sh`
checks it, both from a clean checkout with lean-ski beside it.

What an accepted proof of a row says, by which theorems:

- **The statement is Lean's.** The verifier (`verify.sh`) never takes the term from the
  file: `lake exe nockstatement --check` recomputes `share (compiled f s)` (`--unshared`:
  `compiled f s = nockToSki f ⬝ encLit s`) from the public formula and subject and
  compares. So the term proved is the compiler's on the formula, by construction.
- **The term evaluates to the product's encoding** (`Nock2Ski/Embed.lean`,
  `Nock2Ski/Share.lean`): `compiled_value : NockEval s f (.val p) → ∃ ep, Enc p ep ∧
  WSteps (compiled f s) ep`, an instance of `embed_value`, and `compiled_crash : NockEval s
  f .exit → WSteps (compiled f s) errT`; `shared_value` and `shared_crash` are the same of
  `share (compiled f s)`, by `share_red : WSteps (share t) t` (one β per binding,
  `abs_beta_close`; the substituted result is literally `t`). lean-nock's `countUp_correct`
  and `HoonOne.dec_correct`, `dec_underflow` supply the `NockEval` hypotheses for the three
  programs.
- **An accepted proof is an evaluation** (lean-ski, `Ski/Circuit/BaseSound.lean`):
  `Circuit.export_sound : sameAirsB Rs (baseAirs t) = true → Accepted Rs ts → ∃ C Mm Pg,
  ts = [C, Mm, Pg] ∧ Accepts (memOf Mm) t C.h (rowOf C) ∧ ∃ v, decode … = some v ∧ Eval t v`.
  ski-air's verifier exports the AIRs it verifies with and has `lake exe circuit compare`
  check them against `Circuit.baseAirs t` for the public term, the first hypothesis; the
  STARK's acceptance is the second (Plonky3's soundness assumed, as in lean-ski's release).
  `lake exe aircheck` accepts the witness table ski-air wrote, `Air.checkA`, hence
  `Air.Accepts` and `checkB_eval`'s evaluation, independently of the STARK.
- **The join** (`Nock2Ski/Share.lean`): `Eval t v` is head reduction to a weak head normal
  form; `shared_value`'s `WSteps` is weak reduction, anywhere in the term. `enc_whnf : Enc
  p ep → Whnf ep` (every encoding is `S ⬝ _ ⬝ _` or `K ⬝ _`), so `Eval ep ep`; lean-ski's
  `eval_back : WSteps t u → Eval u v → ∃ v', Eval t v' ∧ WSteps v' v` gives `Eval t v'` with
  `WSteps v' ep`, and `Eval.deterministic` makes `v' = v`. That is `eval_enc : Enc p ep →
  WSteps t ep → Eval t v → WSteps v ep`, and the rows' statements are
  `shared_value_eval : NockEval s f (.val p) → Eval (share (compiled f s)) v → ∃ ep, Enc p
  ep ∧ WSteps v ep`, `shared_crash_eval : NockEval s f .exit → Eval (share (compiled f s))
  v → WSteps v errT`, and `compiled_value_eval`, `compiled_crash_eval` for a `plain` row.
- **Together**: *an accepted proof of a row is a proof that the Nock formula evaluates on
  the subject to the product, with the statement recomputed by Lean*: the proof's final
  state `v` (the `decode` of `export_sound`) weakly reduces to an encoding of Nock's
  product, both weak head normal forms, so `v` is that encoding up to reduction inside its
  fields (`Whnf.wstep`), `Cell`-, `Atom`- or `Err`-headed as the product is. Conversely
  (M4e, `Nock2Ski/Converse.lean`), an accepted proof of a row shows Nock has an outcome
  at all: `shared_terminates : Eval (share (compiled f s)) v → ∃ o, NockEval s f o`, and
  `embed_outcome` reads it off the final state, an encoding of a Nock value or `Err` for a
  Nock crash, so the row's statement needs no `NockEval` hypothesis from lean-nock. Binding
  the product as a public value, read from `v` by probing, is M4's probe step
  (`air_probe_decodes`); the hidden subject is M4c's, below.

### Hidden subjects (`release/nock/hidden/`, M4c)

Two programs over an atom the prover keeps secret, proved in zero knowledge on lean-ski's
composed predicate circuit (`Ski/Predicate.lean`, `Ski/Circuit/CompPred.lean`), with no
Nock circuit: the statement "I know an atom `n` of 8 bits with `*[n f] = p`" for the
spec's count-up `dec` (`countup_hidden_7`: `p = 6`, witness 7; 42,221 machine rows,
84,181 memory cells, CPU 2^16, memory 2^17, proved in 5.3 s, proof 762 KB, verified in
1 s) and for Hoon's `++dec` taking its sample from the subject (`hoon_dec_hidden_12`:
`p = 11`, witness 12; 101,927 rows, 183,911 cells, 2^17, 2^18, 10.0 s, 818 KB, 1 s).
`release/nock/RESULTS.md` has the table. The statement is lean-ski's predicate shape: the
verifier `V`, a closed term, applied by the circuit to the public `x` and the `k` literal
bits `ρ` in its layout (`boolsT`: a `pairT` chain, the last bit alone, each cell
constrained to `K` or `K I`), must reach `K`. Here

    V = nockPredV f k = share (λ x ρ. eqn (nockToSki f (Atom (toBitsT k ρ))) x),  x = encNoun p

`toBitsT k` converting the `k` bits to the runtime's canonical bit list (trailing zeros
stripped: `toBitsT_red`, `trim_bits`), so the compiled formula runs on exactly `encNoun
(.atom n)` for `n` the bits' value, and `eqn` (`eqn_enc`) answers `K` exactly when the
product's encoding is `encNoun p`'s. What is proved (`Nock2Ski/Pred.lean`):

- **The statement is Lean's.** `nockpred --check` recomputes `nockPredV f k` and
  `encNoun p` from the public formula and product and compares the statement, and ski-air
  has lean-ski's `lake exe composed statement` confirm the bytes are exactly the composed
  machine's text before it proves or verifies.
- **Completeness**, `nock_pred_complete : 0 < k → n < 2^k → NockEval (.atom n) f (.val p)
  → Eval (nockPredV f k ⬝ encNoun p ⬝ boolsT (bitsK k n)) K`: from `nockPredV_beta`
  (`share_red` and `absN_beta_close`), `toBitsT_red` with `trim_bitsK`,
  `embed_value_encNoun` and `eq_enc`'s `eqn_enc`. lean-nock's `countUp_correct 6` is the hypothesis for the
  first statement; for the second, `HoonOne.dec_correct 11 ctx` is the battery's run on the
  core with sample 12, and the formula's opcode 8, 10 and 9 steps around it are three
  `NockEval` constructors (neither is composed in Lean here: `Nock.Comp` and `Nock.HoonOne`
  import `Nock.Fuel`, which clashes with `Ski.Basic`, below); `nockpred --run` shows the
  acceptance in the clear (17,141 and 41,249 contractions).
- **Soundness**, `nock_pred_sound : 0 < k → bs.length = k → Eval (nockPredV f k ⬝ encNoun
  p ⬝ boolsT bs) K → ∃ n, n < 2^k ∧ WSteps (eqn ⬝ (nockToSki f ⬝ encNoun (.atom n)) ⬝
  encNoun p) K ∧ (∀ q, NockEval (.atom n) f (.val q) → q = p) ∧ ¬ NockEval (.atom n) f
  .exit`. The hypothesis is what lean-ski's `Circuit.predExport_sound` concludes of an
  accepted proof of `predAirs V x k W` (the bits `bs` are the proof's memory, `slotBits`),
  with Plonky3's soundness assumed as in lean-ski's release. The first conjunct is the
  SKI-level fact, the one every lean-ski statement makes about its term: *the SKI
  compilation of `f`, on the hidden atom, is `eqn`-equal to `p`'s encoding*. The last two
  carry it to Nock as far as the one-directional simulation allows: by
  `embed_value_encNoun` and Church–Rosser (`wsteps_K_iff`), any Nock value on `n` is `p`,
  since `eqn` answers `F` on unequal encodings and `F` never reaches `K` (`F_not_K`); by
  `embed_crash_encNoun` and `eqn_err`, Nock does not crash on `n`.
- **Termination** (M4e, `Nock2Ski/Converse.lean`, below): Nock terminates on `n`, so the
  Nock reading of an accepted proof is `*[n f] = p` outright: `nock_pred_sound_nock : 0 < k
  → bs.length = k → Eval (nockPredV f k ⬝ encNoun p ⬝ boolsT bs) K → ∃ n, n < 2^k ∧
  NockEval (.atom n) f (.val p)`. Until M4e the converse simulation (a SKI value implies a
  Nock value) was open and the reading was "`*[n f]` is `p` if it is anything, and it is
  not a crash".
- **The join is read across two Lean environments.** `Ski.Predicate` and
  `Ski.Circuit.CompPred` cannot be imported beside lean-nock: `Ski.Composed` reaches
  `Ski.Words` (through `Ski.AirProbe`, `Ski.ProbeTree`, `Ski.Decode`), whose root-level
  `inductive Outcome` (`Ski/Words.lean:157`) clashes with lean-nock's `Outcome`
  (`Nock/Eval.lean:62`); and `Nock.Fuel`'s `Diverges` (`Nock/Fuel.lean:678`) with
  `Ski.Basic`'s (`Ski/Basic.lean:136`). So `boolsT` in `Pred.lean` is a copy of
  `CompM.boolsT`, `PredText.lean` copies the statement's rendering (checked against the
  original at every use by ski-air), and `nock_pred_sound`'s hypothesis is
  `predExport_sound`'s conclusion by inspection, not by one `obtain`. Namespacing either
  library's `Outcome` (and `Diverges`) would close it; neither repository is modified
  here. Zero knowledge is lean-ski's `comp_zk`, for any composed statement.

### Cell-shaped hidden subjects (`release/nock/hidden/`, M4d)

Hoon's compiled `++add` (`urbit/benchmark/desk/bar/add.nock`) over two hidden atoms, the
statement "I know atoms `a` and `b` of `k` bits each with `*[[a b] f] = p`":
`hoon_add_hidden_3_4` (`p = 7`, witness `[3 4]`, `k = 4`; 94,646 machine rows, 197,147
memory cells, CPU 2^17, memory 2^18, proved in 10.7 s, proof 824 KB, verified in 1.4 s,
prover peak 1.9 GB) and `hoon_add_hidden_6_57` (`p = 63`, witness `[6 57]`, `k = 6`;
225,556 rows, 352,360 cells, 2^18, 2^19, 20.2 s, 879 KB, 1.4 s, 3.4 GB).
`release/nock/RESULTS.md` has the table and the instances that did not fit (`[20 30]` at
`k = 6` is 638,260 contractions, past the composed statement's 2^20 height cap; `[8 30]`
proved at 2^19 but peaked at 5.1 GB). The subject is a public **skeleton** with hidden
atoms at its leaves (`Nock2Ski/PredSkel.lean`): `Skel` is `hole w` (a hidden atom of `w`
bits), `lit n` (a public noun) or `cell l r`; the circuit holds one comb of `N` bits, the
holes' widths summed, laid out left to right, and the verifier

    V = nockPredS f sk = share (λ x ρ. eqn (nockToSki f (skelT N sk 0 ρ)) x),  x = encNoun p

cuts the comb into the holes' slices (`dropT k`: the comb after `k` bits, `λρ. ρ (K (dropT
(k-1)))`; `takeT k`: the comb of the first `k`, `λρ. ρ (λ b r. pairT b (takeT (k-1) r))`;
`sliceT N off w` uses the comb itself for a single hole, `dropT off` for the last hole and
`takeT w` after `dropT off` otherwise), converts each with M4c's `toBitsT w`, and rebuilds
the subject with `cellT` and `atomT` around them. `[?k ?k]` is `pairSkel k`, the verifier
`nockPred2V f k`; a one-hole skeleton is M4c's verifier term for term (`nockPredS_hole :
nockPredS f (.hole k) = nockPredV f k`), so `nockpred` takes a skeleton in place of the bit
count everywhere (`8` means `?8`) and the M4c files are unchanged. What is proved:

- **The slices are `take` and `drop`**: `dropT_red : k < bs.length → dropT k ⬝ boolsT bs ↠
  boolsT (bs.drop k)`, `takeT_red : 0 < k → k < bs.length → takeT k ⬝ boolsT bs ↠ boolsT
  (bs.take k)`, `sliceT_red`; and **the rebuilt subject is the filled skeleton's
  encoding**, `skel_red : bs.length = N → sk.ok → off + sk.width ≤ N → skelT N sk off
  (boolsT bs) ↠ encNoun (sk.fill (bs.drop off))`, where `sk.fill bs` fills the holes left
  to right with their slices' values (`sk.ok`: every hole has a bit, as `toBitsT`
  requires).
- **Completeness**, `nock_predS_complete : sk.ok → bs.length = sk.width → NockEval (sk.fill
  bs) f (.val p) → Eval (nockPredS f sk ⬝ encNoun p ⬝ boolsT bs) K`, and its instance
  `nock_pred2_complete : 0 < k → a < 2^k → b < 2^k → NockEval [a b] f (.val p) → Eval
  (nockPred2V f k ⬝ encNoun p ⬝ boolsT (bitsK k a ++ bitsK k b)) K` (`pairSkel_fill`:
  the two halves of the witness are `a` and `b`). `nockpred --run` shows the acceptance
  in the clear (38,189 and 91,007 contractions).
- **Soundness**, `nock_predS_sound : sk.ok → bs.length = sk.width → Eval (nockPredS f sk ⬝
  encNoun p ⬝ boolsT bs) K → WSteps (eqn ⬝ (nockToSki f ⬝ encNoun (sk.fill bs)) ⬝ encNoun
  p) K ∧ (∀ q, NockEval (sk.fill bs) f (.val q) → q = p) ∧ ¬ NockEval (sk.fill bs) f
  .exit`, and `nock_pred2_sound : 0 < k → bs.length = 2k → Eval (nockPred2V f k ⬝ encNoun
  p ⬝ boolsT bs) K → ∃ a b, a < 2^k ∧ b < 2^k ∧ …` the same of `[a b]`. The last two
  conjuncts are M4c's `nock_pred_sound_val` and `nock_pred_sound_crash`, now stated over
  any subject. The hypothesis and the join to lean-ski's `Circuit.predExport_sound` are as
  in M4c; Nock's termination on the hidden subject is M4e's `nock_predS_sound_nock : sk.ok
  → bs.length = sk.width → Eval (nockPredS f sk ⬝ encNoun p ⬝ boolsT bs) K → NockEval
  (sk.fill bs) f (.val p)` and `nock_pred2_sound_nock : … → ∃ a b, a < 2^k ∧ b < 2^k ∧
  NockEval [a b] f (.val p)`.
- **The witness side**: `Skel.bitsOf sk s` gives the bits of a subject under the skeleton
  when it fits (`nockpred --witness`); it is not proved inverse to `fill`, since the
  theorems are stated on `fill` of the bits the circuit holds.

### The converse simulation (`Nock2Ski/Converse.lean`, M4e)

`embed_value` and `embed_crash` carry a `NockEval` derivation to the compiled term; the
hidden-subject statements above needed the other direction, that a compiled term which
reaches a weak head normal form came from a Nock run with an outcome, and until M4e stated
the Nock claim conditionally ("`*[n f]` is `p` if it is anything"). M4e proves it:

- **`embed_terminates : Enc s es → Eval (nockToSki f ⬝ es) v → ∃ o, NockEval s f o`**, and
  `nockI_terminates` for the interpreter on encodings of the subject and the formula.
  Then `embed_outcome : Enc s es → Eval (nockToSki f ⬝ es) v → (∃ p ep, NockEval s f (.val
  p) ∧ Enc p ep ∧ WSteps v ep) ∨ (NockEval s f .exit ∧ WSteps v errT)`, `embed_complete`
  (a weak head normal form that does not reduce to `Err` is an encoding of Nock's value),
  and PLAN §2.4's `embed_diverges : Enc s es → (Diverges (nockToSki f ⬝ es) ↔ ∀ o, ¬
  NockEval s f o)`, lean-ski's `Diverges`. The three-valued contract is now exact in both
  directions, on all of Nock 4K.
- **The argument** is by contraposition through a measure on each side, not through the
  fuel interpreters (lean-nock's `Nock.Fuel` cannot be imported beside `Ski.Basic`, and
  nothing of it is needed: `Nock.Eval` suffices). On the Nock side, `Pending n s f`
  (`Nock2Ski/Pending.lean`) is a derivation cut off after `n` costed steps: an inductive
  over `NockEval` whose constructors mirror `NockEval`'s premises, one operand pending and
  the earlier operands (in lean-nock's order) with values; every constructor costs one
  except the static hint, which the compiler erases. `pending_of_noOut : (∀ o, ¬ NockEval
  s f o) → Pending n s f` for every `n`, classically: at a node with no outcome some
  operand has none. On the SKI side, `HLen t N` (`Nock2Ski/Head.lean`) is "`t` reaches a
  weak head normal form in exactly `N` head contractions", with lean-ski's three facts
  (`Ski/Converse.lean`, copied since that module reaches `Ski.Words`): a head reduction of
  `j` steps leaves `N - j` (`hlen_steps`), a weak reduction anywhere leaves at most `N`
  (`hlen_wsteps`, from `par_step_le`), and `t ⬝ a` normalizing makes `t` normalize in no
  more steps (`hlen_app`).
- **`pending_both : Pending n s f → Enc s es → HLen (nockToSki f ⬝ es) N → n ≤ N`**, and
  the same of `nockIFix ⬝ es ⬝ ef` for `Enc f ef`, one induction for both halves as
  `embed_both`. Each case follows `embed_both`'s weak reduction to the point where the
  pending operand sits as the argument of `force` (`cel`, `inc`, `ifn`), and there the
  operand's head length is strictly below the node's, because `force X k` head-reduces to
  `X` applied to its four continuations in at least one contraction. Those head
  reductions are computed symbolically and kernel-checked: `hred` is lean-ski's `ostep?`
  iterated at the head of an open term with a count (`hred_stepsN`, by `OStep.close`), and
  `pendCheck`/`contCheck` are the decidable shape checks `decide +kernel` runs on
  `forceT.toO ⬝ₒ .var 0 ⬝ₒ .var 1` and its siblings (headed by the operand's variable with
  four arguments; or by the continuation's variable with one argument that weakly
  normalizes to the operand's encoding, for `force` on an `Atom`, `Cell` or `Form`),
  `hlen_force_pend`, `hlen_force_enc`, `hlen_cel_pend`, `hlen_inc_pend`, `hlen_ifn_pend`,
  `hlen_ifn_zero`, `hlen_ifn_one`, `hlen_eqn_pend`. When the pending operand comes after
  values, `embed_both` supplies the values' encodings and `hlen_force_enc` the strict
  step; the interpreter's dispatch needs only the weak-reduction lemmas it already had
  (`nockO_O2`, `nockOK5_beta`, …), since its strict step is the same `force`. So a term
  normalizing in `N` steps leaves Nock not pending at `N + 1`, hence with an outcome.
- **The corollaries**: `nock_of_eqn_K : eqn (nockToSki f ⬝ encNoun s) (encNoun p) ↠ K →
  NockEval s f (.val p)` (`eqn` forces its first argument, `hlen_eqn_pend`, so the
  compiled term normalizes and `embed_terminates` gives the outcome, which
  `nock_pred_sound_crash` and `nock_pred_sound_val` identify), and from it
  `nock_pred_sound_nock`, `nock_predS_sound_nock`, `nock_pred2_sound_nock` above, and
  `compiled_terminates`, `shared_terminates` for the base-circuit rows. Axioms:
  `propext`, `Classical.choice`, `Quot.sound`, the contraposition being classical.
