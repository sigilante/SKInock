# skinock — Nock in SKI, with its jets: the plan

Started 2026-11-03. Open question C5 of `../OPEN-QUESTIONS.md`. Companion paper:
`~/Documents/1 Projects/Davis2027 Nock in SKI/`.

## Status (2026-11-04)

- **Compiler built** (`python/skinock`, SKIjack route): opcodes 0–11 and autocons, strict
  in Nock's places in Vere's order, crashes as `Err`, literal formulas carrying code
  (`Form`). urbit/benchmark `norm/tests.json`: 63/63 agree with the Python oracle, on
  aviary and on Avon. Hoon's compiled `++dec` runs: about 220 contractions per Nock step,
  3,000 DAG nodes after hash-consing literals and formula bodies (the first version
  duplicated code per nesting level and reached 1.1 M atoms).
- **M0 done**: lean-nock builds on Lean 4.31.0 (merged to its master); skinock's Lake
  package requires both by path.
- **One environment** (2026-11-04, lean-nock branch `namespace-nock`): every lean-nock
  declaration is under `namespace Nock` (`Nock.Outcome`, `Nock.Diverges`, `Nock.Term`,
  `Nock.Word`, …; nothing re-exported), so `Nock.Fuel`, `Nock.Comp`, `Nock.Mock`,
  `Nock.HoonOne` import beside `Ski.Basic`, `Ski.Words` and `Ski.Circuit`. skinock's modules
  `open Nock`; the joins below that were read across two Lean environments are now
  theorems: `Nock2Ski/Circuit.lean` (`probe_proof_nock`, `probe_table_nock`,
  `pred_proof_nock`, `predS_proof_nock`, `pred2_proof_nock`: lean-ski's
  `Circuit.probeExport_sound_tree` and `Circuit.predExport_sound` composed with
  `probe_value`/`probe_decodes_nock` and `nock_pred*_sound_nock`), `JetTransport.lean`
  (`dec_transport`, `add_transport` unconditional, `JetWord` imported), and
  `Nock2Ski/PredNock.lean` (the released statements' completeness from lean-nock's
  `countUp_correct`. The Hoon `dec` rows come from lean-nock's battery- and clue-generic
  `dec_body_correct` (branch `hoon-dec-general`; the released battery differs from `decBat`
  only in its `~_` (`%mean`) hint's clue), and `++add` from `nockF_sound` on `decide +kernel`
  (it differs from `addBat` in the context layout, so `add_correct` does not compose). `Value.lean`, `JetSpec.lean` and `Pred.lean`'s `boolsT` remain as the
  vocabularies the light and heavy modules share; `PredText.lean`'s copies of
  `ComposedText` remain (tooling, byte-checked by ski-air).
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
- **M2 done** (`Nock2Ski/Compile.lean`, `Enc.lean`, `Embed.lean`, `bench/NormCheck.lean`):
  `nockToSki` over autocons and opcodes 0–11; `lake exe normcheck` runs the 63 reference
  tests and the two `dec` programs through it, 63/63 and 6/6; `embed_crash` closed for every
  `NockEval` constructor; `embed_value` closed in the form "an encoding of the value, or
  `Err`", the `Err` disjunct being exactly opcode 2/9 on a code-free formula (M1's `app`
  has no `nockI`). The statement is over an encoding relation `Enc` with code optional on
  formula-shaped cells, since the product's term is not a function of the noun (`[1 [0 1]]`
  returns a `Form`). Opcode 10 takes lean-nock's order (tree, then patch); `compile.py` and
  `nock.py` have the patch first and should be changed. Remaining for the strong
  `embed_value` on all of Nock: pin `nockI` (needs Front to tie mutual recursion) and prove
  `app` with the fallback simulates `NockEval`; or M3's `fragment_static`, under which the
  `Err` disjunct cannot arise.
- **Opcode 12** built as an extension: a resolver over a fact table (`scry`), default crash;
  the interpreter restructured to a single recursive equation so Front can pin it (M3).
- **M3 done** (`Nock2Ski/Decls.lean`, `InterpDefs.lean` … `Interp.lean`, `InterpEnc.lean`,
  `Embed.lean`): the interpreter fallback pinned and simulated, `embed_value` strong. Two
  more edits to `nock.ski` were needed for Front to accept it: the restructure had left the
  cycle `appI → nockP → nockO → appI` and three direct `nockI` calls in `nockO` (skijack ties
  such a group with one `Y` over a tuple; Front ties only self-recursion), and the
  interpreter's opcode 12 evaluated its operands before `scry = Err`, where lean-nock,
  nock.py and the compiled code crash first (`Malformed`); now `op12 ev s t` is supplied by
  the compiler, `Err` by default. Every equation is pinned to Front's output (`x_pin`) and
  its structure kernel-checked (`x_eq`), the terms equal Python's character for character
  (`terms/*.ski`), and `embed_both` is one induction on `NockEval` for the compiled term and
  the interpreter together (mutual through `app`/`appI` and `nockI` on a `Form`).
  `nockI_crash`, `nockI_value`, and `embed_value`/`compiled_value`/`embed_value_encNoun`
  without the `Err` disjunct. `normcheck`: 63/63, 6/6, and the 63 tests interpreted 63/63.
  Kernel memory was the constraint: the parse is pinned once against the parsed
  declarations, each equation's term is defined as the file's (so the two sides of `x_eq`
  share the kernel's work), and the kernel-heavy theorems are spread over a chain of modules
  so that each `lean` process stays within about 4 GB.
- **M4a done** (`bench/NockStatement.lean`, `release/nock/`): the first Nock program proved on
  lean-ski's base circuit with no Nock circuit. `lake exe nockstatement NAME FORMULA SUBJECT`
  prints the corpus row of `compiled f s` (prefix term and head contraction count, `runF`'s,
  which is ski-air's machine's: `--count-term` on lean-ski's `sumto_us.term` gives its
  reference 10297); `--check` recomputes a row from the formula against a corpus on stdin, the
  verifier's Lean half. `release/nock/produce.sh` writes the rows and runs `ski-air`;
  `verify.sh` recomputes them, re-proves (the base path has no verify-only entry point and
  writes no proof file: the proof is made and checked in-process) and has `aircheck` accept
  the table. Count-up `dec` at 7: 12,004 contractions, 29,591 rows (2.465 per contraction,
  sumto's 2.435), CPU height 2^15, memory 2^18, proved in 1.8 s, verified in 1.2 s. Hoon's
  `++dec` at 12 and at 0 (the crash) recompute and count correctly (28,324 and 1,468
  contractions, 2.47 and 2.46 rows each) but are refused for their heights: `encLit`
  encodes a battery's nested formula literals once per nesting level, so the term is
  2,154,393 cells, 2.7% over the memory table's 2^21, and ski-air loads it without sharing
  (`heights [17, 22, 22] out of bounds`). Sharing nested code in the compiler (Python's DAG
  of the same program is about 6,000 nodes) is the fix, and it moves the pinned terms, so it
  is M4's. Left for M4 proper: decoded products via probes (`air_probe_decodes`), hidden
  subjects via the composed predicate circuit on `encNoun s`, and the joining lemma that an
  `Enc` is a weak head normal form, so `Eval.deterministic` identifies the circuit's result
  with `embed_value`'s encoding.
- **M4b done** (`Nock2Ski/Share.lean`, 2026-11-04): sharing in the term. `share t`
  hash-conses `t`, binds every repeated subterm of `shareMin = 1024` cells or more with a λ,
  smallest first, as the let chain `(λx₁. (λx₂. … C) L₂') L₁'` by bracket abstraction, so the
  prefix tree is the DAG's size; `share_red : WSteps (share t) t`, one `abs_beta_close` per
  binding, the result literally `t` (checked, `shareWith`, so the hash-consing is outside the
  trusted path); `shared_value`, `shared_crash`. The joining lemma: `enc_whnf : Enc p ep →
  Whnf ep`, and with lean-ski's `eval_back` and `Eval.deterministic`, `shared_value_eval :
  NockEval s f (.val p) → Eval (share (compiled f s)) v → ∃ ep, Enc p ep ∧ WSteps v ep` (the
  circuit's final state weakly reduces to an encoding of the product; `WSteps`, not equality,
  since `embed_value` is weak reduction and the state is a weak head normal form with
  reductions pending inside its fields), `shared_crash_eval`, and the `compiled_*_eval` twins.
  Hoon's `++dec` falls from 2,154,393 cells to 60,217 (28 bindings); the βs cost 17% more
  contractions (33,043 against 28,324; the crash row 4,606 against 1,468). Both Hoon rows
  proved: `hoon_dec_12` 81,895 rows, CPU 2^17, memory 2^18, 2.4 s; `hoon_dec_0` 11,364 rows,
  2^14, 2^17, 0.8 s; the run peaked at 1.32 GB. The threshold is a trade (cells against
  contractions, `nockstatement --cells`): at 32 the chain is 368,077 cells and 316,721
  contractions, since every variable in scope costs a `K` per body and an `S`/`K` spine per
  use, paid once per forced copy. Lower-overhead binding (B/C-style combinators, or scoping
  each binding at its uses' common ancestor) would cut the contraction cost if it matters.
  Python's hash-consing is the DAG analogue; Avon's `dag` form carries it.
- **M4c done** (`Nock2Ski/Pred.lean`, `PredText.lean`, `bench/NockPred.lean`,
  `release/nock/hidden/`, 2026-11-04): a Nock program over a **hidden** atom, proved in zero
  knowledge on lean-ski's composed predicate circuit, no Nock circuit. The statement "I know
  an atom `n` of `k` bits with `*[n f] = p`": verifier `nockPredV f k = share (λ x ρ. eqn
  (nockToSki f (Atom (toBitsT k ρ))) x)`, `x = encNoun p`, `toBitsT k` converting the
  circuit's `boolsT` bits to the canonical `bitsT` list (`toBitsT_red`, `trim_bits`).
  `nock_pred_complete` (from `embed_value_encNoun`, `eqn_enc`); `nock_pred_sound`: an
  accepted proof shows bits of value `n < 2^k` with `eqn (nockToSki f ⬝ encNoun (.atom n))
  (encNoun p) ↠ K`, hence any Nock value on `n` is `p` and Nock does not crash on `n`
  (`eqn_err`); Nock's termination on `n` is the converse simulation, M4e's. `lake exe
  nockpred` writes the statement in `ComposedText.publicTextC`'s format and the witness,
  `--check` is the verifier's Lean half; `ski-air composed-prove`/`composed-verify` prove and
  check. Count-up `dec` at hidden 7 → 6: 42,221 rows, CPU 2^16, memory 2^17, 5.3 s, 762 KB
  proof, verified in 1 s; Hoon's `++dec` with the sample from the subject, hidden 12 → 11:
  101,927 rows, 2^17, 2^18, 10.0 s, 818 KB (the shared verifier 63,223 cells). Found: the
  two libraries could not be imported together (`Outcome` in `Ski/Words.lean:157` and
  `Nock/Eval.lean:62`; `Diverges` in `Nock/Fuel.lean:678` and `Ski/Basic.lean:136`), so the
  composition with `Circuit.predExport_sound` was by inspection and `boolsT`, `predStmt`,
  `publicTextC` copied; lean-nock's `namespace Nock` closed it (`pred_proof_nock`, above).
- **M4d done** (`Nock2Ski/PredSkel.lean`, `bench/NockPred.lean`, `release/nock/hidden/`,
  2026-11-04): a **cell-shaped** hidden subject. The subject is a public skeleton `Skel`
  (`hole w` a hidden atom of `w` bits, `lit n` a public noun, `cell l r`); the circuit holds
  one comb of `N` bits, the holes' widths summed, and the verifier `nockPredS f sk = share
  (λ x ρ. eqn (nockToSki f (skelT N sk 0 ρ)) x)` cuts it with `takeT`/`dropT` (`sliceT`),
  converts each slice with `toBitsT`, and rebuilds the subject with `cellT`/`atomT`
  (`skel_red`: exactly `encNoun (sk.fill bs)`). A one-hole skeleton is M4c's verifier term
  for term (`nockPredS_hole`), so `nockpred` takes a skeleton everywhere (`8` is `?8`) and
  M4c's files stand. `nock_predS_complete`/`nock_predS_sound` for any skeleton,
  `nock_pred2_complete`/`nock_pred2_sound` for `[?k ?k]` (`nockPred2V`). Hoon's compiled
  `++add` (`urbit/benchmark/desk/bar/add.nock`) over hidden `[3 4] = 7` at `k = 4`: 38,189
  contractions, 94,646 rows, 197,147 memory cells, CPU 2^17, memory 2^18, 10.7 s, 824 KB
  proof, verified in 1.4 s, prover peak 1.9 GB; `[6 57] = 63` at `k = 6`: 91,007
  contractions, 225,556 rows, 352,360 cells, 2^18, 2^19, 20.2 s, 879 KB, 3.4 GB. The tree
  is 11.1 M cells (`add`'s core nests `dec` and `inc` as batteries), shared 84–85 K with 41
  bindings. `add` loops `dec` which loops `inc`, so the cost is about `a²/2`: `[20 30]` at
  `k = 6` is 638,260 contractions, past the composed statement's 2^20 cap
  (`ComposedText.logOK`, though ski-air's `MAX_LOG_HEIGHT` is 21); `[8 30]` proved at 2^19
  and 2^19 (342,149 rows, 27.4 s) but peaked at 5.1 GB and is not released. Left for M4:
  the probe step for a decoded public product.
- **M4e done** (`Nock2Ski/Head.lean`, `Pending.lean`, `Converse.lean`, 2026-11-04): the
  converse simulation, so the hidden-subject statements are Nock claims. `embed_terminates
  : Enc s es → Eval (nockToSki f ⬝ es) v → ∃ o, NockEval s f o`, `nockI_terminates`,
  `embed_outcome` (the final state is an encoding of Nock's value or `Err` for its crash,
  and Nock does one or the other), `embed_complete`, and §2.4's `embed_diverges : Enc s es
  → (Diverges (nockToSki f ⬝ es) ↔ ∀ o, ¬ NockEval s f o)` with lean-ski's `Diverges`.
  Not by fuel adequacy on both sides as §2.4 planned (lean-nock's `Nock.Fuel` cannot be
  imported beside `Ski.Basic`, and `Nock.Eval` suffices), but by contraposition through a
  measure on each side: `Pending n s f`, a `NockEval` derivation cut off after `n` costed
  steps (the static hint costs nothing, as the compiler erases it), with `pending_of_noOut`
  (no outcome → pending at every `n`, classical); and `HLen t N`, the head length to a weak
  head normal form, with lean-ski's `StepsN.wtail` (weak reduction never lengthens the
  run, `par_step_le`) and `StepsN.app_left` copied from `Ski/Converse.lean` (which reaches
  `Ski.Words`). `pending_both : Pending n s f → Enc s es → HLen (nockToSki f ⬝ es) N → n ≤
  N` and the same of the interpreter, one induction as `embed_both`; the strict step at
  every node is `force` (`cel`, `inc`, `ifn`) on the pending operand, whose head reduction
  to the operand applied to its continuations is computed symbolically (`hred`, lean-ski's
  `ostep?` with a count) and kernel-checked (`pendCheck`, `contCheck`), so the interpreter
  half needs only its existing weak-reduction lemmas. Corollaries: `nock_of_eqn_K`,
  `nock_pred_sound_nock : 0 < k → bs.length = k → Eval (nockPredV f k ⬝ encNoun p ⬝ boolsT
  bs) K → ∃ n, n < 2^k ∧ NockEval (.atom n) f (.val p)`, `nock_predS_sound_nock`,
  `nock_pred2_sound_nock`, `compiled_terminates`, `shared_terminates`. Axioms `propext`,
  `Classical.choice`, `Quot.sound`. The three modules build in seconds; nothing heavy.
- **M4f done** (`Nock2Ski/Value.lean`, `ProbeTree.lean`, `Probe.lean`, `bench/NockProbe.lean`,
  `release/nock/probe/`, 2026-11-04): the public product as a public value of the proof.
  lean-ski's probe machinery is generic in the probe tree (`Probe.V`, `DecV`, `Air.planOf`,
  `AcceptsP`, `air_probe_sound`, `checkPA_sound`); only `Probe.toV` and the tooling that
  computes a plan (`bench/Jets.lean` `plan`/`check-probe` from a SKIlark outcome, ski-air's
  `probe.rs::lean_plan` asking `lake exe jets plan OUTCOME`, `circuit compare-probe`) are
  SKIlark's. `nounV p` is the tree of `encNoun p` (`Atom` 0/4 with the bits, `Cell` 1/4;
  bits `Nil | Cons` 2 markers, bit `T | F` 2); `decV_encNoun`, `probe_complete`;
  uniqueness by determinism of head reduction (`encS_unique`, `err_unique`); `probe_value
  : DecV t.toO (nounV p) → ValueIs t p`; `probe_sound`/`probe_check` from lean-ski's
  theorems; and on the Nock side `probe_decodes_nock : ValueIs (compiled f s) p → NockEval
  s f (.val p)` (`_shared` too) from `embed_outcome`, `probe_complete_nock` for atom
  products. The join was read across the two environments through `Value.lean`'s `ValueIs`
  (one constant both sides import; nothing copied); now `probe_proof_nock`, above. `lake exe nockprobe plan|term|jets|
  check`; Avon's `witness --plan` (its plan reader is generic) ran the segments for
  `countup_dec_7` (6: 8 segments, 12,099 contractions, 29,829 rows) and `hoon_dec_12` (11:
  10 segments, 33,165, 82,203), and Lean's `Air.checkPA` accepts both tables (and the runs
  with lean-ski's 9,259 and 4,146 licensed template roots instantiated: 6,279 and 18,431
  contractions). Released gzipped with plans and jet files; `verify.sh` step 5 checks them
  with Lean alone. A `Form`-shaped cell product has no finite tree (its code field is a
  function); atoms always read, cells when the term is a `Cell`; a code-dropping `toCell`
  wrapper would cover all products.
- **M4g done** (lean-ski branch `probe-plan-file`, commit `a12b13e`; `bench/NockProbe.lean`
  `tree`, `release/nock/probe/NAME.tree`, `NAME.probe.proof`, 2026-11-04): the STARK of the
  probe tables. ski-air took a plan only from `lake exe jets plan OUTCOME`, a SKIlark
  outcome; the branch lets the outcome words be any probe tree written out (`tree`, then
  the nodes in preorder, `c k n` each; `Ski/ProbeText.lean`), accepted by `jets plan`,
  `jets check-probe`, `circuit compare-probe` and so by ski-air's probe commands, which pass
  the words through unchanged (no change to the statement check; every SKIlark form still
  works, lean-ski's `release/verify.sh` step 5 passes), and adds
  `Circuit.probeExport_sound_tree` (generic in the tree, concluding `Probe.DecV t.toO v`;
  `probeExport_sound` is its instance). `ski-air probe-prove-table` proved both released
  tables (2.09 s and 3.41 s, 609,390 and 598,190 bytes, under 0.8 GB) and `probe-verify`
  accepts them for the tree of the product and refuses the product + 1, the cell, a changed
  byte, the other row. The accepted proof instantiates `probe_sound` through
  `probeExport_sound_tree` and `probe_value`; `probe_decodes_nock` gives `*[s f] = p`.
- **M5 done, the theorem and the jetted proofs; the `dec` data-jet circuit held**
  (`Nock2Ski/JetSpec.lean`, `JetWord.lean`, `JetTransport.lean`, `bench/NockProbe.lean`
  `check-jets`, `release/nock/jets/`, 2026-11-04). §3.1's `jet_transport : Leaf f c →
  Implements (nounContract c) (jetT f)`: for a formula `f` with a total model `c` (`Leaf f c
  := ∀ S, NockEval S f (c S)`, lean-nock's leaf-correctness shape), the lean-ski data-jet
  contract `⟨encNoun, encOut, c⟩` (a value as `encNoun`, the crash as `Err`) is implemented
  by `jetT f = λx. toCell (nockToSki f x)`, from `embed_value` and `embed_crash`;
  `nounContract_respects` by `encNoun_inj`; `jet_close`, `jet_real` (`JSteps.close`,
  `real_of_jet`): a verifier accepting under the jet accepts with `jetT f` in its place.
  Instances `dec_transport`, `add_transport` from `leaf_dec`, `leaf_add` (`JetWord.lean`,
  from lean-nock's `leaf_correct`; `decF = phi .dec` by `rfl`). `toCellT` copies a noun's term
  code-free (`toCell_enc`), the wrapper M4f named; needed because `Enc` is a relation (a cell
  may be a `Form`) and `encO` a function. Two-valued against three-valued: `cw` is total and
  two-valued, divergence has no encoding and no row (`embed_diverges`), and for the words it
  does not occur (`word_crash_total`), so `Leaf` is the whole contract; `formContract f` on
  `Dom f = {S // ∃ o, NockEval S f o}` with Nock's outcome as spec, `jet_transport_dom` with no
  hypothesis, is the restriction to the domain. The join, when `Nock.Comp` could not be
  imported beside `Ski.Basic`: `JetSpec.lean` (lean-nock only) as the shared vocabulary,
  `Leaf decF decC` one constant, as `Value.lean` joined the probe step; now `dec_transport`
  is unconditional (above). Not built, by the user's hold: the circuit
  of the transported `dec` data jet (lean-ski's data-jet path needs a precompile computing
  `spec`), and any Avon C jet. **Jetted proofs** with lean-ski's existing supercombinator
  jets (code jets of SKIlark's templates matched in the Nock terms: 9,259 roots in the
  count-up term, 4,146 in Hoon's): `ski-air jets-measure` (Avon's `witness --jet-table`
  writes the same table), `nockprobe check-jets` (`Air.checkJA` bound to the row), `ski-air
  jet-prove`/`jet-verify`, as lean-ski's sumto stage. `countup_dec_7`: 29,591 → 17,716 rows
  (683 instantiations; 12,004 → 6,270 contractions), proved 1.96 s, verified 1.2 s, 553 KB;
  `hoon_dec_12`: 81,895 → 52,084 (1,939; 33,043 → 18,420), 1.42 s, 0.7 s, 503 KB;
  `hoon_dec_0`: 11,364 → 10,275 (164; 4,606 → 3,960), 0.91 s, 0.7 s; prover under 420 MB. The chain:
  `Circuit.jetExport_sound` + `jet_run_shape` + `embed_outcome`. The loop does not collapse
  (§8's gate for M5 named the data jet): rows fall 36–40%, proportional to the count still.
- **The `dec` data jet on lean-ski's circuit** (`Nock2Ski/DecBridge.lean`, `DecLoop.lean`,
  `DecTermNock.lean`, `bench/NockDec.lean`, `release/nock/decloop/`; lean-ski branch
  `dec-loop`, `Ski/DecTermText.lean`, `Ski/DecTerm.lean`; 2026-11-04). The bridge:
  `toNoun`, `encNn_eq`, `encO_eq`, `dec_impl_lean : Implements DecJet.decContract (jetT
  decF)` (discharging `decpreExport_sound`'s `hP`, `decpre_proof_nock`), and the bare word
  `dec_impl_bare : Implements DecJet.decContract (nockToSki decF)` (no `toCell`). lean-ski's
  `decterm J` statement takes any public verifiers open in the jet's atom
  (`dectermExport_sound`, `dectermExport_close`); `nockdec_sound`: for any formula `f`, an
  accepted proof of `verT (checkJ f s p)` (M4c's `eqn` check with every `nockToSki decF` the
  jet) shows `*[s f] = p`. Rows for `*[[N 0] phi(dec)] = [N-1 0]`: jetted 2,184 (N = 10) to
  12,233 (N = 2^32 - 1), one jet row, proved in under 1.4 s; unjetted 48,316 (N = 10),
  252,097 (50), 533,392 (100, 3.3 GB), past the cap at 1,000. The Λ loop `while (top ≠ 0) dec`
  (`decLoop_nock` from `composition_term`) is proved unjetted (`loop_1`, `loop_3`: 190,814 and
  242,656 rows) and **does not collapse**: the jet row reads a subject laid out in memory, and
  inside the compiled loop the word's argument never is (the run stops at the first call,
  `nockdec probe`); a laid-out cell's fields come out of elimination as thunks, so the jet
  cannot fire on its own output either. Collapsing a loop needs a jet that normalises a
  computed argument (§3.2's limit, now measured).
- **Remaining** (M3's other items, M4–M7): `fragment_static` is moot for correctness (the
  fallback is proved) and is a cost statement; the Λ front end; the statement path and the
  circuit.
- **M6, analytic**: `release/nock/COMPARISON.md` sets skinock's measured rows against Zorp's
  NockVMROM row accounting (no per-program numbers in their paper; Nockchain's prover is not a
  stand-alone CLI): about 60–100× the trace area per Nock step before jets. The live run
  remains.
- **In progress**: Avon jets for `inc` and `eq` with the Avon agent (terms pinned in `terms/`).
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
  normal form. (M4e: proved by contraposition through a pending-run relation and the head
  length, not through the fuel interpreters; `Nock2Ski/Converse.lean`.)
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
  with no new proof of the function. (M5: proved as `jet_transport : Leaf f c → Implements
  (nounContract c) (jetT f)` with `jetT f = λx. toCell (nockToSki f x)`, the output copied
  code-free since `Enc` is a relation; `Λ_N w` is lean-nock's `phi w`, the word's formula,
  `cw w` its model; `Nock2Ski/JetTransport.lean`, README "Jet transport".)
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
  probe plan for the public product (`air_probe_decodes`; M4f: `nockprobe plan`, the plan of
  `nounV p`, with `probe_sound`/`probe_decodes_nock` in place of `air_probe_decodes`, whose
  tree is SKIlark's; M4g: `nockprobe tree`, the tree as ski-air's outcome words on lean-ski's
  `probe-plan-file` branch, the probe tables proved and verified).
- The verifier (`ski-air`) pipes the formula bytes to Lean exactly as `skilark statement`
  does, so the term is never trusted from a file. Lean's check is the theorem of §2.4
  instantiated at the formula.
- Public evaluation: the jet circuit (`compj`) with the transported jet table.
  Hidden subject: the composed circuit general in its statement (`compAirsG`), bits
  constrained to `K` or `K I`, the Sudoku and split8 machinery unchanged. (M4c: done as
  `nockpred`, the predicate statement `predicate (nockPredV f k) (encNoun p) k`, one
  hidden atom of `k` literal bits converted by `toBitsT k`. M4d: the cell-shaped hidden
  subject as a public skeleton `Skel` with hidden atoms at its holes, one comb of all the
  bits cut by `takeT`/`dropT`, `nockPredS f sk`; `add` over hidden `[a b]`.)
- Three statements for the demo: `dec n = m` with `n` hidden (M4c); `++dec` on a cell crashes
  (the error outcome is provable, and it is the co-design paper's point that crashes are
  observable); `add a b = c` with `a` and `b` hidden (M4d, unjetted), jetted (M5).

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
| M3 | the interpreter fallback pinned and simulated; `embed_value` strong; then `embed_diverges`, `fragment_static` | `nockI_value`, `nockI_crash`; the 63 tests interpreted; `countUp_zero_diverges` carried to SKI | 1–2 weeks |
| M4 | `nock statement` exe; the verifier's Lean check; the three statements proved on the circuit; rows measured (M4a done: `nockstatement`, count-up `dec` proved on the base circuit; M4b: sharing, Hoon's `++dec`; M4c: hidden subjects on the composed predicate circuit, `nockpred`; M4d: cell-shaped hidden subjects, `add` over two hidden atoms; M4e: the converse simulation, `embed_terminates`, the hidden-subject statements as Nock claims; M4f: the product as a public value, `nounV`, `probe_decodes_nock`, probe tables Lean-checked; M4g: the probe tables proved, ski-air taking the tree as its outcome words on lean-ski's `probe-plan-file` branch) | `release/nock/` with `verify.sh` passing | 2 weeks |
| M5 | `jet_transport` for `dec` and `add`; jetted proofs; the rows table (done 2026-11-04: `jet_transport`, `dec_transport`, `add_transport` closed, `Nock2Ski/JetTransport.lean`; Hoon's own `++dec`, `hoon_dec_transport` on its domain, the body under any hint, `Nock2Ski/HoonDec.lean`, term pinned `terms/jetT-hoonDecBodyF.dag`; jetted proofs with lean-ski's existing template jets, `release/nock/jets/`, rows −36–40%; the transported `dec` data jet's circuit, which would collapse the loop, is held) | the loop collapses; theorem closed | 2–3 weeks |
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
    Embed.lean         embed_value, embed_crash (M2–M3)
    Converse.lean      embed_terminates, embed_diverges (M4e)
    Jet.lean           jet_transport (M5)
    Statement.lean     the nock statement path (M4)
  bench/Nock.lean      lake exe nock
  release/nock/        statements, proofs, verify.sh (M4)
  PLAN.md, README.md
```
