# skinock

Nock in SKI, with its jets. A compiler from Nock 4K formulas to closed SKI terms, built
on [SKIjack](https://github.com/sigilante/SKIjack), checked against
[urbit/benchmark](../../urbit/benchmark)'s reference tests and Hoon-compiled programs on
aviary-kernel and on [Avon](https://github.com/sigilante/avon); and a Lean development
joining [lean-nock](https://github.com/sigilante/lean-nock) (Nock 4K, the three-valued jet
contract, co-derivation) to [lean-ski](https://github.com/sigilante/lean-ski) (SKI, the
heap machine, licensed jets, the circuit). `PLAN.md` is the plan; this file is what exists.

## The opcode walk

`OPCODES.md`: every rule of Nock 4K in order, with its compiled form, its interpreter case,
its Lean step lemmas and the reference tests that cover it.

## The artifact in one command

```
scripts/artifact.sh          # install, test, check, build, prove, verify; prints ARTIFACT OK
scripts/artifact.sh quick    # the same without regenerating the circuit proofs
```

From a clean checkout with lean-ski beside it and lean-nock on its `lean-4.31` branch, it
runs the Python tests (139), urbit/benchmark's reference tests and Hoon programs, the Lean
build with its gates and axiom report, then produces and verifies every circuit proof in
`release/nock`. About six minutes on an Apple M4 Max.

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
jets licensed by theorems. The live run on count-up dec is in `release/nock/ZORP-RUN.md`:
about 280× fewer raw compute rows natively, on a released prover whose scope is the mining
puzzle (opcode 9 and the general memory table are Zorp's pending work).

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
- `Nock2Ski/Value.lean` (M4f): the vocabulary the two sides of the probe step share.
  `EncS n e`, the shape of an encoding of `n` (an atom as `encNoun`, a cell as `Cell` or as
  `Form` with any code; `Enc` implies it), and `ValueIs t p`: `t` has a weak head normal
  form `v`, `v` does not weakly reduce to `Err`, and every encoding-shaped term `v` weakly
  reduces to encodes `p`. Imports `Nock2Ski.Noun` only (lean-nock's `Nock.Basic` and
  lean-ski's `Ski.Compile`, which coexist), so both sides can import it.
- `Nock2Ski/ProbeTree.lean` (M4f, lean-ski's side: imports `Ski.AirProbe`, so not in
  `Nock2Ski.lean`'s root): the probe tree of our encoding, `nounV : Noun → Probe.V` (`Atom`
  constructor 0 of 4 with the bits as its field, `Cell` constructor 1 with two; bits `Nil |
  Cons bit bits`, bits `T | F`, 2 markers each), `nounPlan p = Air.planOf (nounV p) 0`;
  eight kernel-checked head reductions of the constructors applied to markers (`atom_hnf`,
  …, by `ohnf`, lean-ski's `ostep?` iterated); completeness `decV_encNoun : DecV (encNoun
  p).toO (nounV p)` and `probe_complete : WSteps t (encNoun p) → DecV t.toO (nounV p)`;
  uniqueness by determinism of head reduction (`osteps_neutral_det`, no confluence),
  `encS_unique : EncS q ep → OWSteps f ep.toO → DecV f (nounV p) → q = p` and `err_unique`;
  `probe_value : DecV t.toO (nounV p) → ValueIs t p` (the probe closed at `S` converges,
  `Converges.app_left` four times); and the circuit: `probe_sound` (lean-ski's
  `Air.air_probe_sound` at `nounV p`: `Air.AcceptsP` for `planOf (nounV p) b0` with
  licensed roots gives `ValueIs t p`) and `probe_check` (the same of `Air.checkPA`, the
  checker over arrays that `nockprobe check` runs).
- `Nock2Ski/Probe.lean` (M4f, lean-nock's side): `encS_of_enc`, `nock_of_valueIs : Enc s es
  → ValueIs (nockToSki f ⬝ es) p → NockEval s f (.val p)` from `embed_outcome`,
  **`probe_decodes_nock : ValueIs (compiled f s) p → NockEval s f (.val p)`** and
  `probe_decodes_nock_shared` for `share (compiled f s)`; completeness
  `probe_complete_nock : NockEval s f (.val (.atom n)) → WSteps (compiled f s) (encNoun
  (.atom n))` (and `_shared`), the hypothesis of `ProbeTree.lean`'s `probe_complete`, for
  atom products (an atom's encoding is `encNoun`'s), `probe_complete_nock_cell` for a cell
  product whose term is code-free (below, "The product as a public value").
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
- `bench/NockProbe.lean`, `lake exe nockprobe` (M4f; on lean-ski's side, so a separate
  exe): `nockprobe plan PRODUCT` prints the probe plan of `nounV p` (`nounPlan`) in the
  format `lake exe jets plan` prints and ski-air's `probe.rs::parse_plan` and Avon's
  `witness --plan` read (`plan n`, then `base k ctor arity parent field` per segment);
  `nockprobe tree PRODUCT` (M4g) the tree itself as the outcome words ski-air's
  `probe-prove`, `probe-prove-table`, `probe-verify` and `lake exe jets plan` take on
  lean-ski's `probe-plan-file` branch (`tree`, then the nodes in preorder, `c k n` each);
  `nockprobe term CORPUS NAME` the row's term; `nockprobe jets TERMFILE` the term's jet
  file (lean-ski's `JetTable.jetTable` over `allTemplates`, what `jets emit` writes);
  `nockprobe check CORPUS NAME TABLE PRODUCT` runs lean-ski's `Air.checkPA` on a table with
  probe segments (the format of `jets check-probe`) for `nounPlan p`, after binding the
  table's term to the corpus row's: `ACCEPT` is `probe_check`, hence `probe_decodes_nock`.
  `scripts/lean-check.sh` runs the plan, the tree and the check on the released tables as
  its M4f gate.

- `Nock2Ski/Circuit.lean`, `Nock2Ski/PredNock.lean` (after lean-nock's `namespace Nock` (branch `namespace-nock`)): the joins as
  theorems. `Circuit` imports lean-ski's `Ski.Circuit.ProbeRows` and `Ski.Circuit.CompPred`
  beside the simulation: `probe_proof_nock`, `probe_table_nock` (an accepted probe proof or
  table is `*[s f] = p`), `pred_proof_nock`, `predS_proof_nock`, `pred2_proof_nock` (an
  accepted predicate proof shows the hidden subject with `*[s f] = p`). `PredNock` imports
  `Nock.Comp` and `Nock.HoonOne`: the five released programs' runs from lean-nock
  (`countUp_correct`; the Hoon `dec` rows from lean-nock's battery- and clue-generic
  `dec_body_correct` through `Nock2Ski/HoonDec.lean`'s leaf; Hoon `add` by `nockF_sound` on
  `decide +kernel`, since its battery is not lean-nock's), and the released statements' completeness and
  the probe tables' makeability as their instances.

- `Nock2Ski/JetSpec.lean`, `Nock2Ski/JetWord.lean`, `Nock2Ski/JetTransport.lean` (M5): jet
  transport, PLAN §3. `JetSpec` (lean-nock only) is the shared vocabulary: `Leaf f c := ∀ S,
  NockEval S f (c S)`, lean-nock's leaf-correctness shape for a formula against a total C
  model, and the words `dec` and `add` written out (`decF`, `addF`, `decC`, `addC`).
  `JetWord` (lean-nock's `Nock.Comp`, `Nock.Mock`) proves `leaf_dec : Leaf decF decC`,
  `leaf_add` from `leaf_correct`, and `decF_eq : decF = phi .dec` by `rfl`. `JetTransport`
  (importing `JetWord` beside lean-ski's `Ski.DataJet`) proves `jet_transport : Leaf f c →
  Implements (nounContract c) (jetT f)`, the data-jet contract with `spec := c`, its
  unconditional instances `dec_transport`, `add_transport` (`jet_transport leaf_dec`),
  `Contract.Respects` by `encNoun_inj`, the corollaries
  `jet_close`/`jet_real` of `JSteps.close`/`real_of_jet`, and the code-dropping copy
  `toCellT` (`toCell_enc : Enc p ep → toCellT ⬝ ep ↠ encNoun p`). Below, "Jet transport".
- `Nock2Ski/HoonDec.lean` (M5): Hoon's own `++dec` as a proved jet. The arm is
  `hoonDecBodyF` (`= decBat_guardBody`), the gate's battery formula run against the core
  `[bat [sam ctx]]`. Its leaf is `hoon_dec_leaf : LeafOn HoonDecDom hoonDecBodyF hoonDecC`,
  from lean-nock's battery- and clue-generic `dec_body_correct` and `dec_body_underflow`
  (lean-nock branch `hoon-dec-general`). Its transport is `hoon_dec_transport : Implements
  (onContract HoonDecDom hoonDecC) (jetT hoonDecBodyF)`. The benchmark's program
  `dec.nock` is `hoon_dec_bench`. Below, "Hoon's own `++dec`".
  `Nock2Ski/HoonDecFree.lean` states the jet on real cores, whose battery and context carry
  code: `hoon_dec_enc` over any `Enc`, `hoon_dec_free_cl` for any terms at axes 2 and 7 with
  either cell a `Form`, the `Err` shapes for any bits, and the fire check `hoonDecFire?`
  with `hoon_dec_fire_sound`. The `*_bare` family (`hoon_dec_bare_fire_sound`, and so on) is
  the same for the bare arm `nockToSki hoonDecBodyF`, which is what a compiled program
  actually contains (`terms/nockToSki-hoonDecBodyF.dag`). `hoon_dec_bare_fire_sound_red`
  lets the reader reduce the argument first. Why the jet does not yet fire in whole programs,
  with the measurements: `release/nock/DECJET.md`, "In whole programs".

## Proofs (`release/nock/`, M4a, M4b, M4c, M4d, M4e, M4f, M4g; M5 below)

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
  the product as a public value of the proof, read from `v` by probing, is M4f's probe step
  (below, "The product as a public value"); the hidden subject is M4c's, below.

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
  `embed_value_encNoun` and `eq_enc`'s `eqn_enc`. The released statements are instances
  (`Nock2Ski/PredNock.lean`): `countup_hidden_7_complete` from lean-nock's `countUp_correct
  6` (the released text is `countUp` by `rfl`), and `hoon_dec_hidden_12_complete` from
  `hoonDecHidden_eval`, the instance at 12 of `hoonDecHidden_gen`. The released `++dec`
  battery is lean-nock's `decBat_guardBody` under a *different* `~_` (`%mean`) clue formula
  (`hoonDecBat_parts`), and `dec_correct`/`dec_loop_inv` are stated on `decBat` itself, so
  the run comes from lean-nock's battery- and clue-generic `dec_body_correct` (branch
  `hoon-dec-general`) through `hoon_dec_hinted_leaf`. Before that, it was lean-nock's fuel
  interpreter run by the kernel (`nockF_sound` on `decide +kernel`). `nockpred --run` shows the acceptance in the clear (17,141 and 41,249
  contractions).
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
- **The join is one theorem** (`Nock2Ski/Circuit.lean`): `pred_proof_nock : 0 < k →
  sameAirsB Rs (predAirs (nockPredV f k) (encNoun p) k W) = true → AcceptedP Rs ts → ∃ n,
  n < 2^k ∧ NockEval (.atom n) f (.val p)`, lean-ski's `Circuit.predExport_sound` composed
  with `nock_pred_sound_nock` (one `obtain`; `boolsT` in `Pred.lean` is `CompM.boolsT`
  restated, `boolsT_eq`). Until lean-nock's `namespace Nock` (branch `namespace-nock`) the two libraries could not be imported
  together (`Ski.Composed` reaches `Ski.Words`, whose root-level `Outcome` clashed with
  lean-nock's; `Nock.Fuel`'s `Diverges` with `Ski.Basic`'s) and the join was read by
  inspection across two Lean environments. `PredText.lean` still copies the statement's
  rendering (tooling, checked against the original at every use by ski-air). Zero
  knowledge is lean-ski's `comp_zk`, for any composed statement.

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
  the two halves of the witness are `a` and `b`). The released statements are its
  instances `hoon_add_hidden_3_4_complete`, `hoon_add_hidden_6_57_complete`
  (`Nock2Ski/PredNock.lean`), from `hoonAdd_3_4`, `hoonAdd_6_57`: lean-nock's fuel
  interpreter run by the kernel (the benchmark's `++add` is not lean-nock's `addBat`, so
  `add_correct` does not apply). `nockpred --run` shows the acceptance in the clear (38,189
  and 91,007 contractions).
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
  fuel interpreters (nothing of lean-nock's `Nock.Fuel` is needed: `Nock.Eval` suffices).
  On the Nock side, `Pending n s f`
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

### The product as a public value (`release/nock/probe/`, M4f, M4g)

The rows above prove evaluation to a weak head normal form `v`; that `v` encodes Nock's
product is `embed_outcome`, a Lean fact the proof does not name. lean-ski's probe circuit
(`Ski/AirProbe.lean`) binds an output: the term is applied to one fresh marker atom per
constructor, the run must end at the marker of the constructor it is with its fields on
the stack, and each field is probed in turn, one **segment** per node of a **probe tree**
(`Probe.V`, `node c k ch`: the `c`-th of `k` constructors with fields `ch`), the segments
laid out depth first as the public **plan** (`Air.planOf`). Its theorem is generic in the
tree: `Air.air_probe_sound : AcceptsP M (load t) roots jets (planOf v b0) p fld row →
RootsOK (load t).heap roots jets → DecV t.toO v`, and `Air.checkPA_sound` the same of the
checker over arrays. Only its instance is SKIlark's: `air_probe_decodes` reads the tree
through `Probe.toV`, the tree of a SKIlark `Outcome` (`err`, or `val` and a stack of
numbers), and so does every tool that computes a plan.

M4f gives the tree of our encoding and proves what an accepted table says of Nock:

- **The tree** (`Nock2Ski/ProbeTree.lean`): `nounV p`, the probe tree of `encNoun p`:
  `Atom` is constructor 0 of 4 with one field, its bits (`Nil | Cons bit bits`, 2 markers,
  `T | F` 2 markers); `Cell` constructor 1 with two. The product 6 (bits `F T T`) is 8
  segments and 18 markers, 11 (`T T F T`) 10 and 22. `decV_encNoun : DecV (encNoun p).toO
  (nounV p)` by eight kernel-checked head reductions of the constructors on their markers,
  so `probe_complete : WSteps t (encNoun p) → DecV t.toO (nounV p)`: the prover can make
  the table whenever the row's term reaches the code-free encoding, which an atom product
  always is (`probe_complete_nock`, from `compiled_value` and `Enc.atom_inv`).
- **What a reading says** (`probe_value`): a term that reads as `nounV p` converges (its
  probe closed at `S` reaches `S` applied to one or two fields, a weak head normal form,
  and lean-ski's `Converges.app_left` strips the four markers), does not weakly reduce to
  `Err`, and every encoding-shaped term its weak head normal form reaches encodes `p`
  (`ValueIs t p`). The uniqueness lemmas `encS_unique`, `err_unique` need only determinism
  of head reduction (`osteps_neutral_det`): a probe that weakly reduces to `var c ⬝ fields`
  head-reduces to that spine with weakly reducing fields (`owsteps_spine`), and the
  reading's spine is the same spine. `probe_sound` and `probe_check` are `air_probe_sound`
  and `checkPA_sound` at `nounV p`, concluding `ValueIs t p`.
- **To Nock** (`Nock2Ski/Probe.lean`): `probe_decodes_nock : ValueIs (compiled f s) p →
  NockEval s f (.val p)` and `probe_decodes_nock_shared`, from `embed_outcome`: the final
  state encodes Nock's value or is `Err` for its crash; `ValueIs` rules out `Err` and names
  the value. **So an accepted probe table for the plan of `p` on a row's term is a proof of
  `*[s f] = p` with `p` a public input of the proof.**
- **The join is one theorem** (`Nock2Ski/Circuit.lean`): `probe_proof_nock`, lean-ski's
  `Circuit.probeExport_sound_tree` (below, M4g) composed with `probe_value` and
  `probe_decodes_nock`, concluding `NockEval s f (.val p)` from an accepted proof against
  `probeAirs (compiled f s) roots jets (planOf (nounV p) 0)`; and `probe_table_nock`, the
  same of a table `Air.checkPA` accepts, through `probe_check`. `ProbeTree.lean` and
  `Probe.lean` still each import one side, meeting in `Nock2Ski/Value.lean`'s `ValueIs`
  (until lean-nock's `namespace Nock` (branch `namespace-nock`) they could not be imported together, `Ski.AirProbe` reaching
  `Ski.Words`, whose root-level `Outcome` clashed with lean-nock's, and the join was read
  across two environments). The prover's side is `countup_dec_7_probe`, `hoon_dec_12_probe`
  (`Nock2Ski/PredNock.lean`): the released rows' terms reach the products' encodings, from
  lean-nock's runs through `probe_complete_nock`.
- **A `Form` product has no tree.** A cell product's term may be a `Form` (constructor 2,
  three fields, the third its compiled code, `Enc.form`): probing the code would run the
  formula on markers, and a plan gives every field a tree (`Seg.arity = ch.length`,
  `endRow`), so no finite plan reads it. The plan is for the code-free shape, which every
  atom has; a cell product is covered when its term is a `Cell` (`probe_complete_nock_cell`).
  A closed `toCell` term that copies a noun dropping code, applied to the row's term, would
  cover every product; not done.

**Run** (`release/nock/probe/`, `produce.sh probe`, `verify.sh` step 5). For
`countup_dec_7` (product 6) and `hoon_dec_12` (product 11): `nockprobe plan` writes the
plan, `nockprobe jets` the term's jet file (lean-ski's `jetTable` licenses 9,259 and 4,146
template roots inside the Nock terms: SKIlark's supercombinator templates match generic
bracket-abstraction subterms), and Avon runs the segments (`avon witness --plan`, its plan
reader is generic, `src/probe.c`): 12,099 contractions and 29,829 rows for the count-up row
(95 contractions over the row's 12,004 to read the product), 33,165 and 82,203 for Hoon's
(122 over 33,043); with the jet table instantiated, 6,279 contractions, 17,760 rows and 688
instantiations, and 18,431, 52,139 and 1,945. Lean's `nockprobe check` (`Air.checkPA`)
accepts all four tables in 0.5–1.6 s (the plain tables padded to 2^15 and 2^17 rows, 2^18
cells) and refuses them for the product + 1 and for a cell. The plain tables are released
gzipped (0.7 and 1.0 MB), with the plans and jet files; `verify.sh` recomputes the plan and
the jet file from the product and the corpus term and checks the table without Avon.

**The STARK (M4g; `probe/NAME.tree`, `probe/NAME.probe.proof`).** ski-air's `probe-prove`,
`probe-prove-table` and `probe-verify` took their plan only from `lake exe jets plan
OUTCOME`, a SKIlark outcome (`err | val n…`, `Probe.toV`; `bench/plonky3/src/probe.rs`
`lean_plan`, `bench/Jets.lean` `parseOutcome`, `bench/Circuit.lean` `parseOutcomeC` for
`compare-probe`). **This step needs lean-ski's branch `probe-plan-file`** (commit `a12b13e`,
"probe: the output as a literal probe tree"; `produce.sh` and `verify.sh` build ski-air from
the checkout beside this one): the outcome words may be any probe tree written out, `tree`
and then its nodes in preorder, `c k n` each for `V.node c k ch` with `n = ch.length`
(`Ski/ProbeText.lean`, `Probe.vWords`/`Probe.vOfWords`; plain decimal, `c < k`, one spelling
per tree, the same cap of 65,536 segments). `jets plan`, `jets check-probe` and `circuit
compare-probe` take either form; ski-air passes the words through to Lean unchanged, so its
statement check is as it was, and every SKIlark form still works. The branch adds one
theorem, `Circuit.probeExport_sound_tree`: a proof Plonky3 accepts against AIRs that match
`Circuit.probeAirs t roots jets (planOf v 0)` (what `compare-probe` checks, with licensed
roots and numbers that fit) gives `Probe.DecV t.toO v`, for any tree `v`;
`probeExport_sound` is its instance at `Probe.toV o`. `nockprobe tree PRODUCT` writes
`nounV p` in that form; `ski-air probe-prove-table` proves the released table for it
(29,829 rows padded to 2^15, 2.09 s, 609,390 bytes, 447 MB peak; 82,203 rows padded to 2^17,
3.41 s, 598,190 bytes, 783 MB) and `probe-verify` accepts each in 0.7–1.2 s after Lean's
three checks (the jet file for the corpus row, the plan of the tree, the AIRs), and refuses
it for the tree of the product + 1, of the cell `[p 0]`, for `val 6`, with one byte changed,
and offered as the other row's. **The accepted proof instantiates `probe_sound`**
(`Nock2Ski/ProbeTree.lean`): `probeExport_sound_tree` at `nounV p` is `DecV t.toO (nounV
p)`, which `probe_value` makes `ValueIs t p`, the conclusion `probe_sound` draws from
`Air.air_probe_sound` for the checker's `AcceptsP`; and `probe_decodes_nock`
(`Nock2Ski/Probe.lean`) gives the Nock claim, `*[s f] = p`, with `p` read from the public
tree. `release/nock/RESULTS.md` has the numbers and the refusals.

## Jet transport (M5)

PLAN §3's theorem, and the jetted proofs the existing machinery gives. What is a theorem and
what is not built is said plainly in each paragraph; nothing new was jetted (no Avon C jet, no
lean-ski data-jet circuit), by the user's hold.

**The two contracts.** lean-nock licenses a jet for a Λ word `w` by `leaf_correct w : ∀ S,
NockEval S (phi w) (cw w S)` (`Nock/Comp.lean`): the word's Nock formula evaluates on every
subject to exactly the C model's outcome, a value or a crash; `word_jet_sound w : ThreeValued
(phi w) (wordJet w)` (`Nock/Mock.lean`) is the model as a jet meeting the three-valued contract.
lean-ski licenses a data jet (`Ski/DataJet.lean`) by a `Contract α β` (`encI : α → Term`,
`encO : β → Term`, `spec : α → β`) and `Implements c P := ∀ x, P ⬝ encI x ↠ encO (spec x)`; then
`JSteps.close` lets any implementation stand in for the jet and `real_of_jet` says a verifier
that accepts under the jet realizes its atom with the implementation closed in.

**The theorem** (`Nock2Ski/JetTransport.lean`). For a formula `f : Noun` and a total model
`c : Noun → Outcome` with `Leaf f c := ∀ S, NockEval S f (c S)` (`Nock2Ski/JetSpec.lean`):

    nounContract c : Contract Noun Outcome := ⟨encNoun, encOut, c⟩        encOut (.val p) = encNoun p,  encOut .exit = errT
    jetT f := S ⬝ (K ⬝ toCellT) ⬝ nockToSki f                               λx. toCell (nockToSki f x)
    jet_transport : Leaf f c → Implements (nounContract c) (jetT f)
    nounContract_respects c : (nounContract c).Respects                     from encNoun_inj
    jet_close : Leaf f c → σ j = jetT f → JSteps (nounContract c) j t u → WSteps (t.close σ) (u.close σ)
    jet_real  : Leaf f c → σ j = jetT f → JSteps (nounContract c) j (V ⬝ₒ x ⬝ₒ r) K → Real (.atom (V.close σ) x) r

The proof is `embed_value` and `embed_crash` on `encNoun S` (`jet_step`): a value's term is an
encoding `ep` with `Enc p ep`, a crash's is `Err`. The instances are Table C's words,
`decContract := nounContract decC`, `addContract := nounContract addC`:

    dec_transport : Leaf decF decC → Implements decContract (jetT decF)        decF = phi .dec,  decC = cw .dec
    add_transport : Leaf addF addC → Implements addContract (jetT addF)        addF = phi .add,  addC = cw .add

with the hypotheses `leaf_dec : Leaf decF decC` and `leaf_add` proved in
`Nock2Ski/JetWord.lean` from `leaf_correct .dec` and `leaf_correct .add` (`decF_eq`, `addF_eq`
by `rfl`; `decC_eq`, `addC_eq` by cases on the subject). So the data jet for `dec` is licensed
in lean-ski by lean-nock's leaf proof plus the embedding, with no new proof of the function.
Axioms: `propext`, `Classical.choice`, `Quot.sound` on the lean-ski side; `propext`,
`Quot.sound` on the lean-nock side.

- **Why `toCell`, and why the implementation is not `nockToSki f` bare.** `embed_value`'s
  encoding is a relation: a cell's term may be a `Form` carrying its compiled code (a battery
  pushed by `[1 …]`), and a `Form` does not reduce to a `Cell`; a `Contract`'s `encO` is a
  function. `toCellT = Y toCellG` copies a noun's term constructor by constructor, dropping
  code: `toCell_enc : Enc p ep → toCellT ⬝ ep ↠ encNoun p` (induction on `Enc`, the three
  continuations β-reduced by `absN_beta_close`, the constructors by `AtomC_red`, `CellC_red`),
  `toCell_err : toCellT ⬝ errT ↠ errT`. It is the `toCell` wrapper the probe section names as
  not done; `jetT f` is the compiled formula followed by it, two contractions.
- **Two outcomes against three.** lean-ski's `Contract` is total: `spec x` exists for every
  `x : α`. lean-nock's `cw w` is total too, and two-valued; its contract's third value,
  divergence, is the absence of a `NockEval` derivation, has no encoding, and no term
  implements it: `embed_diverges` says the compiled term diverges exactly where Nock has no
  outcome, so no row of any circuit ends there. For the Λ words divergence does not occur
  (`word_crash_total`, by the guards Λ emits), which is what `Leaf f c` states: `c` is the
  whole contract, and `leaf_total : Leaf f c → ∀ S, ∃ o, NockEval S f o`. For a formula that
  does diverge somewhere no total `c` satisfies `Leaf f c`; `formContract f : Contract (Dom f)
  Outcome` restricts the domain to `Dom f = {S // ∃ o, NockEval S f o}`, takes Nock's outcome
  there as the specification (`Classical.choose`), and `jet_transport_dom f : Implements
  (formContract f) (jetT f)` holds with no hypothesis (`formContract_respects` too). That is
  "use `Implements` only on inputs where `NockEval` yields an outcome".
- **One environment.** `JetTransport.lean` imports `JetWord.lean` (lean-nock's `Nock.Comp`,
  `Nock.Mock`) beside `Ski.DataJet`, so `dec_transport` is `jet_transport leaf_dec` with no
  hypothesis; the formulas are lean-nock's by `rfl`. (Until lean-nock's `namespace Nock` (branch `namespace-nock`) `Nock.Comp`
  reached `Nock.Fuel`, whose root `Diverges` clashed with `Ski.Basic`'s, and the instances
  took `Leaf decF decC` as a hypothesis discharged in `JetWord.lean`, the two meeting in
  `JetSpec.lean`'s one constant.)
- **What is not built.** (Since built: lean-ski's `dec` data-jet circuit, branch `dec-jet`,
  and its use on Nock claims, "The `dec` data jet on lean-ski's circuit" below.) The
  transported `dec` data jet had no circuit: lean-ski's data-jet path needs a precompile that
  computes `spec` (its own `Ski/DataJet.lean` says so of Poseidon2). Nor is an Avon C jet for
  `dec` made. `jet_transport` licenses the row: whatever circuit computes `cw .dec` on
  `encNoun` may stand in for `jetT decF`, and a proof accepted under it is a proof about the
  Nock formula. PLAN §3.2's limit stands: the transported jet says nothing about steps.

**Hoon's own `++dec`** (`Nock2Ski/HoonDec.lean`, `terms/jetT-hoonDecBodyF.dag`). The
benchmark's `dec.nock` is a two-arm core. Arm 5 builds the gate `[body [0 core]]`, and arm 4
slams it with the subject (`[8 [9 5 0 1] 9 2 10 [6 0 7] 0 2]`). `body` is lean-nock's
`decBat_guardBody` to the cell, with no hint at all. The released programs' battery and
lean-nock's `decBat` put the same body under Hoon's `~_ leaf+"decrement-underflow"`, a
dynamic `%mean` hint (tag `1851876717`), and differ only in that hint's clue formula. Neither
carries a `%fast` hint: `hoon.hoon`'s `~/ %dec` (`~% %dec +7 ~`) wraps the formula that builds
the gate, outside the battery. So the jet follows the Nock-level split between registration
and matching:

    hoon_dec_leaf       : LeafOn HoonDecDom hoonDecBodyF hoonDecC      from dec_body_correct, dec_body_underflow
    hoon_dec_transport  : Implements (onContract HoonDecDom hoonDecC) (jetT hoonDecBodyF)
    hoon_dec_hinted_leaf tag k : LeafOn HoonDecDom [11 [tag [1 k]] hoonDecBodyF] hoonDecC
    hoon_dec_bench n    : *[n+1 hoonDecBenchF] = n,   hoon_dec_bench_zero : *[0 hoonDecBenchF] crashes

- **Licence**: the computation under any hint, the body against the core. Domain
  `HoonDecDom`: every subject except a core whose sample is a cell. There the arm diverges
  (`hoon_dec_off_domain`, from lean-nock's `dec_body_cell_diverges`), and so does its
  compiled term (`hoon_dec_off_domain_term`). So no total `Leaf` exists, and the contract is
  `onContract`, the `nounContract` shape on a subtype (`jet_transport_on`). The model
  `hoonDecC` is `n` on `[bat [n+1 ctx]]` and the crash everywhere else in the domain.
- **Matched term**: `jetT hoonDecBodyF`, the compiled body. A static hint compiles away
  (`nockToSki [11 t c] = nockToSki c`). A dynamic hint compiles to "evaluate the clue, then
  the body's term". Either way the jettable SKI term is the compiled body, so any `++dec`
  that differs only in a hint over the body matches the same term.
- **Registration**: metadata at the Nock level (for `hoon.hoon`'s `++dec`: name `%dec`,
  parent axis 7, no hooks), outside the licence and outside the matched term.
  `hoon_dec_hinted_leaf` covers any constant-clue hint. lean-nock's `dec_hint_correct`,
  `dec_hint_underflow` and `dec_hint_cell_diverges` cover any clue, each under exactly the
  clue hypothesis its outcome needs.
- **Avon.** An SKI term has no hint to carry registration, so an Avon supercombinator
  jet's identity is its term (structural hash). That is the right design for SKI, and it is
  how the Λ `dec` jet (Avon PR #121, `jetT decF`) is matched. The registration/matching split
  is a Nock-level matter, and it shows up here only in which Nock formula is compiled to the
  matched term: the body, not the hinted battery.
- The released Hoon `dec` rows (`Nock2Ski/PredNock.lean`) are now instances of the leaf for
  every sample (`hoonDecHidden_gen`, `hoonDecF_val`, `hoonDecF_call`). Before, they were the
  fuel interpreter evaluated by the kernel, one input at a time.

**The jet on real cores** (`Nock2Ski/HoonDecFree.lean`). `hoon_dec_transport` is stated over
`encNoun` inputs, which never contain a `Form`. A real compiled gate core `[bat [sam ctx]]`
carries code in `bat` and `ctx` (pushed by `[1 …]`, so `Form`s). The core itself may also be
formula-shaped: under `Enc`, `[bat [n ctx]]` and `[n ctx]` (with `n ≤ 11` read as an opcode)
may each be `formT h t k`, not `cellT h t`. `CellLike x h t` is `x = cellT h t ∨ ∃ k, x =
formT h t k`. Write `⟨m⟩` for `encNoun (atom m)`:

    hoon_dec_enc          : Enc s es → HoonDecDom s → jetT hoonDecBodyF ⬝ es ↠ encOut (hoonDecC s)
    hoon_dec_free_cl      : CellLike s B X → CellLike X ⟨n+1⟩ C → jetT hoonDecBodyF ⬝ s ↠ ⟨n⟩
    hoon_dec_free_cl_zero : CellLike s B X → CellLike X ⟨0⟩ C   → jetT hoonDecBodyF ⬝ s ↠ Err
    hoon_dec_err_atom b   :                                      jetT hoonDecBodyF ⬝ atomT b ↠ Err
    hoon_dec_err_noSample : CellLike s B (atomT b)             → jetT hoonDecBodyF ⬝ s ↠ Err

The first is for any encoding of a domain subject: it comes from `embed_value`/`embed_crash`,
which hold for every `Enc`, and then `toCell_enc` or `toCell_err`. The others are for
**arbitrary closed terms** `B`, `C` and codes `k`, with no `Enc` hypothesis, even divergent
ones. `hoon_dec_free`, `hoon_dec_free_form` and `hoon_dec_free_zero` are the `cellT`/`formT`
instances. The sample must be canonical: `eqT` compares bit lists, so a non-canonical zero is
unequal to the literal `0`. In the two `Err` shapes the atom's bit term `b` is **arbitrary**,
since the arm only cases on the constructor (`hd_atomT`, `tl_atomT`). A cell sample is
excluded, since there the arm diverges (`hoon_dec_off_domain_term`).

The proof runs the compiled arm step by step (`dec_guard`, `dec_pull`, `dec_edit`, `dec_loop`
by induction on the remaining count). Every operation that touches the subject is `hdT`,
`tlT`, `forceT` or the edit walk. Each looks only at the outer constructor of the cell it is
given, and a `Form` answers as a `Cell` does (`hd_form`, `tl_form`, `force_form`, so
`CellLike.hd`/`.tl`/`.force`). The arm pushes the counter and the loop battery, giving the
loop core `[loop [i S]]` with the whole subject `S` copied as a field. The loop reads axis 30
(the sample, through `S`) and axis 6 (the counter). The edit at axis 6 forces `S` only to its
outer constructor. So `B`, `C` and the codes ride along in `S` and are never applied,
projected into or forced. `eqT` and `incT` see only the canonical atoms `⟨m⟩`, `⟨i⟩`, `⟨i+1⟩`.

**The fire check** (`hoonDecFire? : Term → Option Term`, what Avon's check implements):

- **Fire `Err`** (`HoonDecErrFires`) when `t` is literally `atomT b`, or a literal
  `cellT`/`formT` whose tail is literally `atomT b`, for any `b`.
- **Fire with the value** (`HoonDecFires`) when `t` is literally a `cellT`/`formT` of
  `[B [atomT (bl bs) C]]` (inner cell also `cellT`/`formT`), `bs` canonical, and `m = val bs <
  2^32`. The output is `encOut (hoonDecOutN m)`: `⟨m-1⟩` for `m ≥ 1`, `Err` at `0`.
- **Decline** otherwise.

`hoon_dec_fire_sound : hoonDecFire? t = some u → jetT hoonDecBodyF ⬝ t ↠ u`. It is assembled
from `hoon_dec_fires_sound`, `hoon_dec_err_fires`, `hoonDecSample?_sound` and
`cellParts?_sound`. `hoonDecSample?_cl` shows the sample check accepts every cell-like
`[B [⟨m⟩ C]]`. `hoonDecFires_pins` pins all three outcomes by kernel evaluation.

**The bare arm, in whole programs.** A compiled program never contains `jetT hoonDecBodyF`.
It contains `nockToSki hoonDecBodyF`, the code of the battery's `Form`. The arm's outputs on
the fire shapes contain no `Form`, so the family holds without `toCell`, with the same check:
`hoon_dec_bare_enc`, `hoon_dec_bare_cl`, `hoon_dec_bare_cl_zero`, `hoon_dec_bare_err_atom`,
`hoon_dec_bare_err_noSample`, and `hoon_dec_bare_fire_sound : hoonDecFire? t = some u →
nockToSki hoonDecBodyF ⬝ t ↠ u`. `hoon_dec_bare_fire_sound_red` (and
`hoon_dec_fire_sound_red`) adds a reduction `t ↠ t'` of the argument before the check. In
the Lean-compiled `hoon_dec` program the bare arm occurs 3 times unshared and 0 times shared.
In the unshared program Avon applies it to an unreduced core and declines.
`release/nock/DECJET.md` ("In whole programs") has the occurrence counts, the numbers and
what Avon needs.

**Jetted proofs with the existing machinery** (`release/nock/jets/`, `produce.sh jets`,
`verify.sh` step 6). lean-ski's supercombinator jets (`Ski/Inst.lean`, `Ski/JetTable.lean`,
`Ski/AirJet.lean`, `Ski/Circuit/JetSound.lean`) license **code jets**: SKIlark's compiler
templates, generic bracket-abstraction shapes, matched inside the loaded term
(`JetTable.jetTable` over `allTemplates`), and an instantiation row that writes a template's
body for its arguments in one step in place of the β-chain. The Nock terms are bracket
abstraction too, so the tables match them: 9,259 licensed roots in the count-up term, 4,146 in
Hoon's `++dec`, 4,139 in the crash row (`NAME.jets`, the same files as `probe/`). `ski-air
jets-measure` runs each row with the roots instantiated and writes the jetted witness (Avon's
`witness --jet-table` writes the same bytes, compared when Avon is present), `nockprobe
check-jets` accepts it bound to the row (lean-ski's `Air.checkJA`), `ski-air jet-prove` proves
it and `jet-verify` checks the proof against the corpus row and the jet file after Lean's
`jets statement-stdin` check of the file (`Air.rootsOKB`):

| row | plain rows | jetted rows | instantiations | contractions plain → jetted | CPU / POP / INSTW | prove s | verify s | proof |
|---|--:|--:|--:|--:|---|--:|--:|--:|
| `countup_dec_7` | 29,591 | 17,716 | 683 | 12,004 → 6,270 | 2^15 / 2^12 / 2^9 | 1.96 | 1.2 | 553 KB |
| `hoon_dec_12` | 81,895 | 52,084 | 1,939 | 33,043 → 18,420 | 2^16 / 2^13 / 2^10 | 1.42 | 0.7 | 503 KB |
| `hoon_dec_0` | 11,364 | 10,275 | 164 | 4,606 → 3,960 | 2^14 / 2^9 / 2^6 | 0.91 | 0.7 | 505 KB |

The rows fall by 40% and 36% on the two public rows (the crash row, mostly the sharing βs, by
10%); the proofs are proved in 0.9–2.0 s and verified in 0.7–1.2 s, the prover under 420 MB.
These are the generic templates, not a jet for `dec`: the loop runs, every contraction of the
`dec` body is paid, and the rows are proportional to the count; the collapse of the loop to a
constant is the data jet's, not built (above). `release/nock/RESULTS.md` has ski-air's lines.

- **What an accepted jetted proof says**: `Circuit.jetExport_sound` (lean-ski,
  `Ski/Circuit/JetSound.lean`): a proof Plonky3 accepts against AIRs matching `jetAirs t roots
  jets` for the row's term `t`, with `rootsOKB` (which `jets statement` checked) and
  `jetFitB`, is a run of the AIR with instantiation rows (`Air.AcceptsJ`), and by
  `Air.air_sound_jet` it ends on a weak head normal form `v` with `∃ v', Eval t v' ∧ WSteps v'
  v` (`Mach.jet_run_eval`: an instantiation is a weak reduction, `inst_sound_g`) and `∃ v',
  Eval t v' ∧ chead v' = chead v` (`jet_run_shape`). `Eval t v'` is the hypothesis of
  `embed_outcome` through `compiled_terminates`/`shared_terminates` and
  `compiled_value_eval`/`shared_value_eval`/`shared_crash_eval` (`Nock2Ski/Converse.lean`,
  `Share.lean`): `v'` weakly reduces to an encoding of Nock's product or to `Err` for its
  crash, and Nock does one or the other. So `v`, a weak reduct of `v'` and a weak head normal
  form, has the head of that encoding: `Cell`-, `Atom`- or `Err`-headed as the product is
  (`jetExport_sound` + `jet_run_shape` + `embed_outcome`). The product as a public value is the
  probe step's (M4f); the jetted probe runs were measured there and are not released as proofs.
- **The join is read across the two modules**: `jetExport_sound` and `Air.checkJA_sound`
  are lean-ski's (`Ski.Circuit`, `Ski.AirJet`); `embed_outcome` is `Nock2Ski.Converse`'s;
  `Eval t v'` is the shared constant. Both import together now (`Nock2Ski/Circuit.lean`
  imports `Ski.Circuit.ProbeRows`); the composition is not written out, since the jetted
  rows are not released as probe proofs.

## The `dec` data jet on lean-ski's circuit (`release/nock/decloop/`)

lean-ski's `dec` data jet (`Ski/DecJet.lean`, `Ski/Circuit/DecAir.lean`) is a row that reads a
subject `encNn s` from the memory cell by cell and writes `encO (decSpec s)`; its soundness
takes any implementation of `DecJet.decContract` (`Circuit.decpreExport_sound`'s `hP`). Three
pieces join it to Nock.

**The bridge** (`Nock2Ski/DecBridge.lean`). `toNoun : DecJet.Nn → Noun` reads an atom's bits
as their value.

    bits_eq_bitsN      : bits n = bitsN n                                     skinock's bits, lean-ski's bitsN
    encNn_eq           : s.wf → DecJet.encNn s = encNoun (toNoun s)
    encO_eq            : s.wf → DecJet.encO (decSpec s) = encOut (decC (toNoun s))        (decB_bitsN)
    dec_impl_lean      : Implements DecJet.decContract (jetT decF)                       from dec_transport
    decpre_proof_nock  : accepted proof of decpre p → ∃ s r, *[toNoun s phi(dec)] = [p r]
    decF_bare          : nockToSki decF ⬝ encNoun S ↠ encOut (decC S)                     no toCell
    dec_impl_bare      : Implements DecJet.decContract (nockToSki decF)

`dec_impl_lean` discharges `decpreExport_sound`'s hypothesis. `decF_bare` is the word as a
compiled program carries it (no `toCell`): the head of `[[7 [0 2] g] 0 3]` is an atom, whose
encoding is unique (`Enc.atom_inv`), the tail is the subject's own (`[0 3]`, `tl_cellT`), and
`force` and `Cell` rebuild the code-free cell (`force_spec`, `consK_beta`, `CellC_red`).

**Any Nock claim as a `decterm` statement** (`Nock2Ski/DecTermNock.lean`; lean-ski's
`Ski/DecTermText.lean`, `Ski/DecTerm.lean`, branch `dec-loop`). lean-ski's `decterm J`
statement names any public verifiers open in the jet's atom by their cells; an accepted proof
makes each head-reduce with the jet to `K` (`Circuit.dectermExport_sound`), and for `verT C =
λ β w. C` any implementation closed in makes `C` reach `K` (`Circuit.dectermExport_close`).
Here:

    abstJ P t          : t with every occurrence of the subterm P replaced by the jet's atom JD
    abstJ_close        : σ JD = P → (abstJ P t).close σ = t
    checkT f s p       = eqn (nockToSki f ⬝ encNoun s) (encNoun p)                       M4c's check
    checkJ f s p       = abstJ (nockToSki decF) (checkT f s p)                            the word as the jet
    nockdec_sound      : accepted proof for compDAirsG [verT (checkJ f s p)] W → *[s f] = p

for **any** formula `f`: `dectermExport_close` with `dec_impl_bare` closes the jetted check to
`checkT f s p` itself, and `nock_of_eqn_K` reads that as a `NockEval` derivation. `lake exe
nockdec emit|check` writes and recomputes the statement for `f = phi(dec)`, `s = [N 0]`, `p =
[N-1 0]`; `ski-air compd-prove|compd-verify` prove and check it (lean-ski's `composed
statement-dec` reads the `decterm` header).

**Rows** (`release/nock/decloop/RESULTS` below; `produce.sh`, `verify.sh`). Jetted, the word
on the literal subject is one jet row, and the rows follow the bits (the check's `eqn` and the
DEC table's one row per bit pattern). Unjetted, the same check with the bare word runs the
word's count-up loop `N` times, about 2,100 contractions a unit:

| N | jetted rows (jet rows) | memory cells | prove s | unjetted rows | unjetted prove s |
|--:|--:|--:|--:|--:|--:|
| 10 | 2,184 (8) | 5,705 | 0.44 | 48,316 | 2.2 |
| 50 | | | | 252,097 | 5.1 |
| 100 | 3,158 (11) | 6,962 | 0.43 | 533,392 | 14.1 (3.3 GB) |
| 1,000 | 4,200 (14) | 8,298 | 0.73 | about 9.7 M (3,923,405 contractions; past 2^21) | |
| 10,000 | 5,484 (18) | 9,904 | 0.73 | | |
| 100,000 | 6,518 (21) | 11,191 | 0.73 | | |
| 1,000,000 | 7,570 (24) | 12,487 | 0.75 | | |
| 2^32 - 1 | 12,233 (36) | 18,066 | 1.32 | | |

Each jetted proof is about 1 MB, verified in 0.55–0.67 s, the prover under 0.7 GB; lean-ski's
`composed check-dec-run` replays each run (every row a step or `DecJet.decRow`, one jet row).
At `N = 100` the jet saves 169× the rows; at `N = 1,000` the unjetted run does not fit the
circuit.

**The Λ loop, and why it does not collapse** (`Nock2Ski/DecLoop.lean`). `decLoop = while (top
≠ 0) dec` on `[n [0 r]]` (test `over over eq ifte(over inc, over)`, body `dec`):

    decLoop_nock : *[[n [0 r]] NT decLoop] = [0 [0 r]]                 composition_term + CEval by induction on n
    decLoop_ski  : nockToSki (NT decLoop) ⬝ encNoun [n [0 r]] ↠ e,  Enc [0 [0 r]] e

Unjetted on the base circuit (shared, 256,825 cells): `loop_1` 76,395 contractions, 190,814
rows, 5.1 s; `loop_3` 96,718, 242,656 rows, 6.8 s (`loop_10` is 239,560 contractions,
`loop_20` 643,783: quadratic, `n` words each running its count-up loop). Jetted it cannot be
proved: `nockdec probe 3` replaces the word's 13 occurrences in the compiled loop by the jet and
runs a head machine that fires the jet only on a subject laid out as `encNn`, as lean-ski's
row does, and the run stops at the first call (contraction 2,826); the word's argument there
is the loop's computed stack.

**No term can lay the argument out** (`release/nock/DECJET.md`, "Inside a loop, on the
circuit"; lean-ski `Ski/NoLayout.lean`, branch `dec-norm`). A normaliser `norm` with `J ⬝
(norm ⬝ x)` readable would have to write the encoding's wrappers, each an application cell
whose function is a constant. On lean-ski's write-once machine an invariant of every
reachable state (`inv_step`, `inv_reach`) makes the `S` that writes such a cell continue
with constant code (`S_cont_const`), so a continuation carrying the rest of a traversal
receives a computed cell `R` only folded, as the thunk `K R w`. `release/nock/decloop/layout`
has the evidence (`layout.txt`, recomputed by produce.sh and verify.sh). A 12-leaf term does
exactly that fold. No term of up to 10 leaves hands `K P` over bare (318,380,772 terms per
goal), and none of up to 9 lays out a cell of two computed fields (405,331,348 terms, both
stack orders).

**The row through thunks fires** (route B; `release/nock/DECJET.md`, "Route B"). lean-ski's
`Ski/DecInd.lean` gives the row `DecJet.decRowI`, which follows `K R w`
at every pointer of the subject's need tree and once at a cell's tail slot:
`decRowI_step` reads it back as a jet step up to `K`-contraction and `HSteps.close_K`
closes a run to `K` with any implementation of the unchanged contract. `Nock2Ski/DecNorm.lean`
gives the continuation-passing normaliser:

    norm_enc    : Enc s es → normT ⬝ es ⬝ k ↠ k ⬝ encNoun s
    normJ_impl  : Implements decContract P → Implements decContract (S normT (K P))
    normDec_enc : Enc s es → S normT (K (nockToSki decF)) ⬝ es ↠ encOut (decC s)

On lean-ski's heap machine (`lake exe nocknorm run 1 3 10 20`, `release/nock/decloop/
results-norm.txt`), the loop's check with every occurrence of the word replaced by
`S normT (K J)` fires the jet at every call and reaches `K`: 7,051 / 14,139 / 39,730 / 77,294
contractions at `N` = 1, 3, 10, 20 against 8,434 / 23,459 / 136,500 / 466,653 unjetted on the
same machine.

**On the circuit** (lean-ski branch `dec-thunk`): DEC reads through the thunks (an
indirection row kind; the `Cell` row's tail slot through one thunk; a list's last `Cons` marks
its step, and the chain ends at a nil that ends a list), its soundness re-proved
(`CompDOK.jetRow` concludes `decRowI`; `decpreExport_sound`, `dectermExport_close`).
`Nock2Ski/DecLoopNorm.lean` makes the loop a `decterm` statement, the word's occurrences
`S X (K J)` under one shared `X = normT` (`nockLoopV`, `lake exe nockdec emit-loop`):

    nockloop_close : accepted proof of nockLoopV f s p →
                     replT (nockToSki decF) (normJ (nockToSki decF)) (checkT f s p) ↠ K

The jet fires at every call: 17,544 / 35,165 / 98,777 / 192,219 CPU rows and 20 / 64 / 238 /
508 DEC rows at `N` = 1, 3, 10, 20 (`ski-air compd-measure`), against 20,757 / 57,785 /
336,681 / 1,152,824 unjetted. Not done: the Nock claim from `nockloop_close` (the compiler's
correctness with the replacement and its converse; `normDec_enc` is the per-call fact), and
the proofs, whose `2^22`-row memory table (the statement's heap is the program as a tree, 2.35
million cells) is past the 4 GB budget (a first form of `loop_1` proved and verified at a
13.5 GB peak). The released `dec_N` proofs are re-produced on the new DEC table (one DEC row
more per bit list; lean-ski `todo/dec-norm.md`).
