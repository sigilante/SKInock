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
