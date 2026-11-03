# skinock — Nock in SKI, with its jets: the plan

Started 2026-11-03. Open question C5 of `../OPEN-QUESTIONS.md`. Companion paper:
`~/Documents/1 Projects/Davis2027 Nock in SKI/`.

## Status (2026-11-03, evening)

- **Compiler built** (`python/skinock`, SKIjack route): opcodes 0–11 and autocons, strict
  in Nock's places in Vere's order, crashes as `Err`, literal formulas carrying code
  (`Form`). urbit/benchmark `norm/tests.json`: 63/63 agree with the Python oracle, on
  aviary and on Avon. Hoon's compiled `++dec` runs: about 220 contractions per Nock step,
  3,000 DAG nodes after hash-consing literals and formula bodies (the first version
  duplicated code per nesting level and reached 1.1 M atoms).
- **M0 done**: lean-nock builds on Lean 4.31.0 on its `lean-4.31` branch (four edits, all
  six gates pass, uncommitted there); skinock's Lake package requires both by path.
- **Measured** (§7 item 1, first numbers): 150–270 contractions per Nock step on aviary's
  copy mode, 110–170 on Avon's share mode, across dec, add, factorial, fibonacci, ackermann
  and bigslot; Avon runs dec 10,000 (16.8 M contractions) in 0.3 s from the `dag` form.
  Opcode 12 crashes, as Vere does outside `+mock`.
- **Done since**: the interpreter fallback `nockI` (about 8× the compiled code; every
  reference test also passes with the formula supplied as data).
- **M1 done** (commit 8c558f4): encodings and all primitive specs proved, terms pinned to
  SKIjack's output through lean-ski's front end (`compileDecls`, since `compileFile` refuses
  the `noun` type's shape). Known limit for M2: Front does not tie mutual recursion, so the
  interpreter fallback is not pinned; either extend Front or state `nockI` separately.
- **In progress**: for formulas built from data (§2.3's
  dynamic case); Lean M1 (`Nock2Ski/Noun.lean`, `Prims.lean`); Avon jets for `inc` and `eq`
  with the Avon agent (terms pinned in `terms/`).
- **Design change against §2.2**: the embedding is *strict*, not lazy. Nock evaluates every
  subformula to a complete noun, so a lazy embedding would return values where Nock
  crashes (`[7 [0 0] [1 42]]`). Only opcode 6's branches are deferred, which is Nock's own
  behaviour. With forces nested in Vere's order the crash-versus-divergence race of §9
  resolves identically on both sides, so `embed_crash` can be stated exactly against
  lean-nock's semantics.
- **Design change against §2.3**: no static fragment analysis is needed. Code is attached
  to literal formulas at compile time and travels with them as data; opcode 2 and 9 use it
  when present and fall back to `nockI` otherwise. The "Hoon-shaped fragment" is then a
  dynamic property (every formula that reaches 2 or 9 carries code), which Hoon's output
  satisfies because batteries are literals pushed by `[1 …]`.

## 0. What this is, and what it is not

`skinock` is the Lean development that joins `lean-nock` (`~/Code/lean-nock`, Nock 4K
semantics, the three-valued jet contract, co-derivation over the concatenative source Λ) to
`lean-ski` (`../lean-ski`, SKI semantics, the heap machine, supercombinator and data jets, the
Plonky3 circuit). It proves one thing and demonstrates one thing.

- **The theorem.** A translation of Nock formulas to closed SKI terms that preserves
  evaluation in the three-valued sense (value, crash, divergence) and carries jet obligations
  across: a jet licensed under lean-nock's contract is a licensed data jet in lean-ski.
- **The demo.** A Nock program, Hoon's compiled `++dec` and the Λ words `dec add sub`, proved
  in zero knowledge by lean-ski's circuit, over a hidden subject, with its loop collapsed by
  the transported jet. No Nock circuit is written. The verifier takes the Nock formula as
  public input and has Lean recompute the SKI term.

It is not a Nock runtime (Avon runs the terms it produces), not a new circuit (lean-ski's is
fixed and audited), and not a Nock-in-SKI interpreter as its main route (that is the slow
path, §2.4).

## 1. The programs

Fixed in advance so the embedding is built against something real. All exist in lean-nock
with proofs on the Nock side.

| program | where in lean-nock | why |
|---|---|---|
| count-up `dec` (the spec's) | `countUp_correct`, `countUp_zero_diverges`, `countUp_cell_diverges` | the loop; diverges at 0 and on a cell, so all three outcomes appear |
| Hoon's compiled `++dec` | `HoonOne.lean`: `decBat`, `dec_correct`, `dec_underflow`, `dec_cell_diverges` | a real gate core: opcode 9 pulls, opcode 8 pushes, crash on underflow |
| Λ words `dec add sub` and the Class D schemas | `Comp.lean`, `Composition.lean`, `leaf_dec`, `leaf_add`, `leaf_sub` | the co-derivation route (§5.2) |
| a one-armed gate core from a Λ program | `gate_term`, `gate_program` | the kernel-shaped statement, matching SKIjack's door |

Opcodes needed: 0–9. Opcode 10 (edit), 11 (hint) and 12 (scry) are §6.

## 2. The embedding

### 2.1 Nouns

A noun is a Scott sum `Atom bits | Cell a b`: an atom is a bit list least-significant first
(`BitArith.bl`, leading zeros allowed), a cell a pair. The tag is what opcode 3 reads. This
differs from the USTJ 3.2 embedding, which represents no nouns at all (its arguments are
Nock nouns and its values are formulas); here nouns are data so the subject can be hidden.
`Ski/Door.lean` already proves axis pulls over untagged cells; the tagged version is the same
chain of projections under one case.

### 2.2 Formulas are static; the subject is dynamic

A Nock formula is a noun, but in a program text it is a literal tree, so the translation is a
compiler over formula trees: `nockToSki : Noun → Term`, defined when the noun parses as a
formula. Each opcode is one SKI combinator applied to the compiled operands:

| opcode | compiles to |
|---|---|
| 0 b | the projection chain of axis b (`Front.axisSteps`), under the tag case |
| 1 b | `K ⟨b⟩`, the constant noun |
| 2 b c | §2.3 |
| 3 | the tag case: `Cell → 0`, `Atom → 1` |
| 4 | `BitArith` increment on the atom's bits; crash on a cell |
| 5 | structural equality of nouns (an `EQ5`-shaped recursion over the sum) |
| 6 b c d | the loobean case over `b`'s result, lazily: `c` and `d` are thunks, only the chosen one runs |
| 7 b c | composition: `c` applied to `b`'s result |
| 8 b c | push: `c` applied to the pair of `b`'s result and the subject |
| 9 b c | `c`'s result is a core; pull axis b of it and apply to the core (§2.3) |
| autocons | the pair of the two compiled formulas' results |

Crashes (slot out of range, 3/4/5 on the wrong shape) compile to the `Err` outcome of
ski-in-ski's extended object language, so the three-valued contract has a place to land.
Laziness is the one departure from USTJ 3.2's embedding: opcode 6's branches are thunked, so
`K I Ω`-shaped programs agree with Nock's normal-order spec rather than diverging.

### 2.3 The dynamic-formula problem, and the Hoon-shaped fragment

Opcode 2 evaluates a formula computed at run time, and opcode 9 pulls an arm out of the
subject and runs it. In Nock that is free: formulas are nouns. In SKI it is the quotation
boundary of Proposition 3.1 in the other direction: a noun held in the subject is data, and
running it needs an interpreter. Two cases:

- **Static.** The formula operand of 2 is `[1 f]` with `f` a literal, or the pulled arm at 9
  was placed in the core by a `[1 battery]` in the program text (or by 8 of such). Then the
  compiler knows the code at compile time and embeds it *as a live SKI term in the subject*,
  exactly SKIjack's door convention: arms are terms. Opcode 9 is `Door.pull_at` followed by
  application. This is the **Hoon-shaped fragment**, and every program in §1 is in it.
- **Dynamic.** Anything else: the formula is built from data. The compiler emits a call to
  `nockI`, a Nock interpreter written in SKIjack over the noun sum (ski-in-ski's method),
  applied to the encoded formula. Correct, about a thousandfold slower per the ski-in-ski
  tower measurements, and never used by the demo.

The fragment boundary is decidable syntactically (a static-formula analysis over the program
text) and is the paper's second theorem: the Hoon-shaped fragment is exactly where the
staging line of SKIjack can be drawn at compile time. This is also the honest reading of
USTJ 3.2's "no readback" limitation from the other side.

### 2.4 Theorems

- `embed_value`: `NockEval s f (.value p)` implies `nockToSki f ⬝ ⟨s⟩` weakly reduces to a
  term that `Decodes` to `⟨p⟩` (the decode relation of lean-ski, since SKI results are equal
  only up to reduction).
- `embed_crash`: `NockEval s f .crash` implies reduction to the `Err` outcome.
- `embed_diverges`: `NockEval s f .diverge` (no outcome) iff the SKI term has no weak head
  normal form, by the fuel adequacy theorem on each side.
- `fragment_static`: on the Hoon-shaped fragment no `nockI` call is emitted, and the
  compiled term's size is linear in the formula's.
- Determinism and order: lean-nock discharged evaluation order against Vere; the embedding
  must pick the same order where it matters (opcode 2's operands, autocons), and `order_*`
  is the reference.

## 3. Jet transport

### 3.1 The statement

lean-nock licenses a jet for a Λ word by `word_jet_sound`: on every subject the C model
punts or meets the three-valued contract. lean-ski licenses a data jet by a contract
`J ⬝ encI x ⟶ encO (spec x)` and `JSteps.close`: any term implementing the contract may stand
in for the jet. Transport:

- `jet_transport`: if `w` is a Λ word with Nock compilation `Λ_N w` and C model `cw`, then
  `nockToSki (Λ_N w)` implements the lean-ski contract whose `spec` is `cw` on encoded nouns.
  So the data jet for `w` is licensed in lean-ski by lean-nock's leaf proof plus `embed_value`,
  with no new proof of the function.
- The converse, for SKI templates that are images of Nock batteries, is a corollary of
  `fragment_static` plus `inst_sound_g`.
- Divergence: lean-ski's jet rows cannot run where the term diverges (a jet that bails there
  is the observable divergence `+mock` exposes, PLAN §5 item 2 of lean-ski). `embed_diverges`
  is what makes the two notions coincide.

### 3.2 What does not transport

Cost. Nock has no fuel and Vere never needs a jet's cost; SKI programs are fuelled and the
circuit charges rows. The transported jet licenses a value and says nothing about steps.
The paper states this as a limitation and measures it: rows of the unjetted loop against
the jetted one, per program, at several atom sizes.

## 4. The statement path and the circuit

- `lake exe nock statement FORMULA SUBJECT-SHAPE`: parses the Nock formula, checks it is in
  the fragment, emits the SKI term and the hidden-bit layout (atoms of the subject as literal
  bits under a public cell skeleton, the `predStmt` shape of `Ski/Predicate.lean`), and the
  probe plan for the public product (`air_probe_decodes`).
- The verifier (`ski-air`) pipes the formula bytes to Lean exactly as `skilark statement`
  does, so the term is never trusted from a file. Lean's check is the theorem of §2.4
  instantiated at the formula.
- Public evaluation: the jet circuit (`compj`) with the transported jet table.
  Hidden subject: the composed circuit general in its statement (`compAirsG`), bits
  constrained to `K` or `K I`, the Sudoku and split8 machinery unchanged.
- Three statements for the demo: `dec n = m` with `n` hidden; `++dec` on a cell crashes
  (the error outcome is provable, and it is the co-design paper's point that crashes are
  observable); `add a b = c` with `a` and `b` hidden, jetted.

## 5. Routes to jets

### 5.1 Direct: Nock jet → SKI data jet (§3)

The contract's `spec` is `cw`; the implementation is the embedded formula. This is the route
the paper proves.

### 5.2 Co-derivation: Λ → Nock and Λ → SKI from one source

Λ is concatenative, as SKIlark's Joy is. A Λ-to-SKIlark front end would make the Nock
compilation and the SKI compilation two targets of one source, with the leaf contracts
stated once at the source and the composition theorem shared. This is the cleaner theory
and the stronger paper claim, and it is where the co-design paper's "co-derivation" is
realized across ISAs. It is §8's stretch item; the direct route is enough for the demo.

## 6. Later opcodes

- 10 (edit): a projection-with-replacement over the noun sum; straightforward.
- 11 (hint): transparent to the composition theorem with a side condition in lean-nock
  (`composition_hint`); in SKI a hint is where a jet root is recognized, so 11 is the natural
  place for the jet table to point.
- 12 (scry, under `+mock`): ski-in-ski's blocking resolver is the SKI scry. Mapping Nock 12
  to `Scry p` with the resolver as the extra parameter makes `+mock` the SKI tower's level 1.
  Not for the demo, but it is the sentence that joins the two virtualization stories.

## 7. Measurements the paper needs

1. Contractions per Nock step under the embedding, per opcode, on the §1 programs
   (ski-phase's tracer counts kinds; its CSV is the table).
2. Rows per program: unjetted, jetted, hidden; against the 2^21 cap.
3. The same programs on Zorp's Nock zkVM (`~/Code/zorp`, ePrint 2025/1110) where it runs
   them, rows and proving time, for the comparison table. The ratio will not favour us per
   step; the audit surface will. Report both.
4. Proving and verifying times on the released configuration (100 queries, blowup 2).

## 8. Milestones

| # | milestone | gate | effort |
|---|---|---|---|
| M0 | one toolchain: lean-nock at `v4.28.0`, lean-ski at `v4.31.0`; bump lean-nock, confirm its audit manifest still passes; `skinock` as a Lake package requiring both by path | `lake build` of a module importing `Nock.Eval` and `Ski.Weak` | days |
| M1 | nouns as the Scott sum; tagged axis pulls; `encNoun`, `decNoun`, opcode 3/4/5 terms with their specs | `pull_tagged`, `inc_spec`, `eq_spec` kernel-checked | 1–2 weeks |
| M2 | the compiler over opcodes 0–9 on the Hoon-shaped fragment; `embed_value` and `embed_crash` | count-up `dec` and `++dec` run through `runF` to the right outcomes; theorems closed | 3–4 weeks |
| M3 | `embed_diverges`; `fragment_static` | `countUp_zero_diverges` carried to SKI | 1–2 weeks |
| M4 | `nock statement` exe; the verifier's Lean check; the three statements proved on the circuit; rows measured | `release/nock/` with `verify.sh` passing | 2 weeks |
| M5 | `jet_transport` for `dec` and `add`; jetted proofs; the rows table | the loop collapses; theorem closed | 2–3 weeks |
| M6 | Zorp comparison; paper draft | numbers in the table; draft to USTJ | 2 weeks |
| M7 (stretch) | Λ → SKIlark front end, co-derivation across ISAs | `composition` shared | open |

Total to a paper: about three months of focused work, M2 and M5 carrying the risk.

## 9. Risks

- **Toolchain.** Two Lean versions. If lean-nock's bump is painful, vendor the four modules
  skinock needs (`Basic`, `Eval`, `Fuel`, `Comp`) with a generator check, as lean-ski does
  for its generated modules.
- **Laziness versus Nock's order.** Nock's spec leaves evaluation order open and lean-nock
  fixed it to Vere's. The embedding is normal order. Where a Nock program's crash depends
  on order (an autocons whose left crashes and whose right diverges), the three-valued
  outcomes can differ. `embed_crash` must be stated relative to lean-nock's chosen order,
  and the paper must say that the embedding is faithful to Vere's Nock, not to every Nock.
- **Cost.** If the embedding costs more than ~100 contractions per Nock step, `++dec` at
  useful atom sizes will not fit 2^21 even jetted at the leaves; then the demo's atoms are
  small and the paper says so.
- **Scope creep.** `nockI`, opcodes 10–12 and the Λ front end are all real and all later.

## 10. Layout (intended)

```
skinock/
  lakefile.toml        requires lean-ski and lean-nock by path
  Nock2Ski/
    Noun.lean          the Scott sum, encNoun, tagged pulls (M1)
    Ops.lean           opcodes 3, 4, 5 as terms with specs (M1)
    Compile.lean       nockToSki, the fragment analysis (M2)
    Embed.lean         embed_value, embed_crash, embed_diverges (M2–M3)
    Jet.lean           jet_transport (M5)
    Statement.lean     the nock statement path (M4)
  bench/Nock.lean      lake exe nock
  release/nock/        statements, proofs, verify.sh (M4)
  PLAN.md, README.md
```
