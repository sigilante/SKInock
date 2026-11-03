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
python -m skinock.check            # urbit/benchmark norm/tests.json: 63/63 agree
python -m skinock.bench dec add    # Hoon-compiled programs at scaled subjects
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
interpreter and is how the tests re-run the reference suite through it.

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

Avon, share mode: dec 100 in 170,905, factorial 5 in 5,092,073, fibonacci 8 in 1,017,378,
bigslot in 8,742,789 contractions, all with the right product. The interpreter fallback
(`nockI`, formulas as data) costs about 8× the compiled code on the same programs.

## The Lean package

`lakefile.toml` requires lean-ski and lean-nock by path; `Nock2Ski/Basic.lean` imports
`Nock.Eval` and `Ski.Weak`. lean-nock must be on its `lean-4.31` branch (four small edits
for Lean 4.31.0, its gates passing). `scripts/lean-check.sh` builds and prints axioms.
