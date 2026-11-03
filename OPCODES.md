# The opcode walk

Nock 4K, in order: autocons, then opcodes 0 to 11; opcode 12 after them, as the extension it
is. For each: the rule, the compiled form (`python/skinock/compile.py`, mirrored by
`nockToSki` in `Nock2Ski/Compile.lean`), the interpreter case (`nock.ski`, `nockO`), the Lean
step lemmas (`Nock2Ski/Embed.lean` for compiled code, `Interp.lean` for the interpreter), and
the urbit/benchmark reference tests that cover it (`norm/tests.json` indices; every one agrees
on the Python oracle, aviary, Avon and the Lean compiler, compiled and as data). Forcing: an
operand that Nock evaluates before use is reduced to a value first by `force` (one case, which
also propagates `Err`), in Vere's order as lean-nock fixed it.

| rule | compiled form | interpreter | Lean step lemmas | reference tests |
|---|---|---|---|---|
| `*[a [b c] d] → [*[a b c] *[a d]]` | force head, force tail, `Cell` | `autocons ev` | `step_autocons` | 0, 1 |
| `0`: `*[a 0 b] → /[b a]` | projection chain of the static axis (`hd`/`tl`), axis 0 → `Err` | `slotB` over the axis bits | `step_op0`, `step_op0_cell`, `step_op0_zero`; `nockO_O0` | 2–12 (11 cases: axes 1–15, axis 0 and into-atom crashes) |
| `1`: `*[a 1 b] → b` | the literal; a formula-shaped literal is a `Form` carrying its code | `t` | `step_op1`; `nockO_O1` | 13–17 |
| `2`: `*[a 2 b c] → *[*[a b] *[a c]]` | force subject, force formula, `app` (a `Form` runs its code, a plain cell goes to `nockI`) | `appI ev` | `step_op2`; `nockO_O2` | 18–21 |
| `3`: `*[a 3 b] → ?*[a b]` | `cel` | `cel` | `step_op3`; `nockO_O3` | 22–25 |
| `4`: `*[a 4 b] → +*[a b]` | `inc` (continuation-style increment of the bits; a cell → `Err`) | `inc` | `step_op4`; `nockO_O4` | 26–30 |
| `5`: `*[a 5 b c] → =[*[a b] *[a c]]` | force both, `eq` (structural, a `Form`'s code ignored) | `eq` | `step_op5`; `nockO_O5` | 31–35 |
| `6`: `*[a 6 b c d] → *[a *[[c d] 0 *[[2 3] 0 *[a 4 4 b]]]]` | `ifn`: force the condition, run only the chosen branch; a non-loobean → `Err` | `ifn` | `step_op6`; `nockO_O6` | 36–40 |
| `7`: `*[a 7 b c] → *[*[a b] c]` | force `b`'s product, run `c` on it | — | `step_op7`; `nockO_O7` | 41–44 |
| `8`: `*[a 8 b c] → *[[*[a b] a] c]` | force `b`'s product, run `c` on `Cell x a` | — | `step_op8`; `nockO_O8` | 45–49 |
| `9`: `*[a 9 b c] → *[*[a c] 2 [0 1] 0 b]` | force the core, pull axis `b`, `app` | `slotB`, `appI ev` | `step_op9`; `nockO_O9` | 50–53 |
| `10`: `*[a 10 [b c] d] → #[b *[a c] *[a d]]` | force the target `d`, then the patch `c` (lean-nock's and Vere's order), rebuild the path with forced projections | `editB` | `step_op10`; `nockO_O10` | 54–58 |
| `11`: `*[a 11 b c] → *[a c]`; `*[a 11 [b c] d] → *[[*[a c] *[a d]] 0 3]` | static hint: `c`; dynamic hint: force the hint, run the body | — | `step_op11_static`, `step_op11_dynamic`; `nockO_O11` | 59–62 |
| shape | a node whose shape lean-nock's `Malformed` rejects compiles to `Err` before its operands | `cel2` guards | `nockToSki_malformed`, `malformed_both` | the crash cases above |
| `12` (not in Nock 4K; `+mock`'s scry) | crash by default, as lean-nock's `Eval.lean:291` ("Opcode 12 does not exist") and Vere outside `+mock`; with a fact table, both operands forced and the resolver `scry` consulted | `op12 ev` | `nockO_O12`, `nockO_Obad` | `tests/test_compile.py::test_op12_scry` |

Beyond the per-opcode lemmas: `embed_value` and `embed_crash` (one induction over every
`NockEval` rule, compiled code and interpreter together), `embed_terminates`, `embed_complete`
and `embed_diverges` (the converse), all in `Nock2Ski/`, with no `sorry`. The three Lean gates
(`lake exe normcheck`) run the 63 tests through the Lean compiler, through the interpreter on
the formula as data, and the six dec programs. Hoon-compiled programs exercising 6, 7, 8, 9, 10
and 11 together: `dec`, `add`, `factorial`, `fibonacci`, `ackermann`, `bigslot` (`README.md`,
Measurements).
