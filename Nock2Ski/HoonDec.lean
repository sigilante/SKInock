import Nock2Ski.JetTransport
import Nock.HoonOne
import Nock.DecDiverges
import Nock.Hint

open Nock Nock.Noun
open Term DataJet

/-!
# Hoon's own `++dec` as a proved jet (M5)

The benchmark's `++dec` (`urbit/benchmark/desk/bar/dec.nock`, `hoonDecBenchF`
below) is a core of two arms.  Arm 5 builds the gate `[body [0 core]]`; arm 4
slams it with the subject as the sample, `[8 [9 5 0 1] 9 2 10 [6 0 7] 0 2]`.
The gate's battery `body` is lean-nock's `decBat_guardBody` to the cell
(`hoonDecBenchF_parts`).  It is the guard `?< =(0 a)` and the count-up loop,
compiled with no hint at all (the benchmark's `dec.hoon` has neither `~/` nor
`~_`).  The released programs of `Nock2Ski/PredNock.lean` (`hoonDecBat`) and
lean-nock's `decBat` push the same body under Hoon's `~_ leaf+"decrement-underflow"`,
the dynamic hint `[11 [%mean c] body]` (tag `1851876717` is `%mean`, a
stack-trace message), with different clue formulas: the constant `[1 …]` in the
released battery, an autocons in lean-nock's.  Neither battery carries a
`%fast` hint.  In `hoon.hoon` the registration `~/ %dec` (`~% %dec +7 ~`:
name `%dec`, parent at axis 7, no hooks) wraps the formula that builds the
gate, outside the battery.

**The split.**  Jet *registration* (a `%fast` clue: name, parent axis, hooks,
recorded by the runtime when the hint runs) and jet *matching* (recognising a
battery at call time and running native code) are separate.  The jet here is
licensed and matched on the computation *under* any hint:

- **licence**: `hoon_dec_leaf : LeafOn HoonDecDom hoonDecBodyF hoonDecC`.  The
  arm is the gate's battery formula `hoonDecBodyF = decBat_guardBody`, run
  against the gate core `[bat [sam ctx]]` (sample at axis 6).  It is proved
  from lean-nock's battery- and clue-generic theorems (`dec_body_correct`,
  `dec_body_underflow`, branch `hoon-dec-general`).  It holds whatever battery
  `bat` sits in the gate slot: the body never reads axis 2.
- **matched term**: `jetT hoonDecBodyF`, by `hoon_dec_transport`.  Any `++dec`
  whose battery differs only in a hint over the body has the same body, so it
  matches the same term.  A static hint compiles away (`nockToSki [11 t c] =
  nockToSki c`).  A dynamic hint `[11 [t h] c]` compiles to `force (H s) (K (C
  s))`: the clue is evaluated, then the body's term runs.  Either way the
  jettable SKI term is the compiled body.  Registration metadata lives at the
  Nock level, outside the matched term.
- **registration**: metadata, not part of the licence.  `hoon_dec_hinted_leaf`
  shows that any dynamic hint with a constant clue over the body (the released
  `hoonDecBat`'s `%mean` is one, and so would be a `%fast`) has the same
  contract.  lean-nock's `dec_hint_correct`, `dec_hint_underflow` and
  `dec_hint_cell_diverges` give the same for any tag and any clue, under
  exactly the hypothesis on the clue that each outcome needs.

**Why `LeafOn`, not `Leaf`.**  `Leaf f c` asks for an outcome on every subject.
Hoon's `++dec` diverges on a cell sample (lean-nock's `dec_cell_diverges`, and
`dec_body_cell_diverges` for any battery), so no total model satisfies
`Leaf hoonDecBodyF c`.  The contract is therefore stated on the subjects
whose sample is not a cell (`HoonDecDom`): `onContract HoonDecDom hoonDecC`.
Off the domain the formula diverges (`hoon_dec_off_domain`), and so does its
compiled term (`hoon_dec_off_domain_term`, by `embed_diverges`).  A jet must
decline there, and the term it stands in for never returns.

`hoonDecC`: on `[bat [n+1 ctx]]` the value `n`; on `[bat [0 ctx]]`, on an
atom, and on `[bat atom]` the crash (the guard's `[0 0]`, or axis 6 missing).
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- Contracts on a domain
-- ---------------------------------------------------------------------------

/-- Leaf correctness on a domain `D`: on every subject in `D`, Nock derives
    exactly `c S`. -/
def LeafOn (D : Noun → Prop) (f : Noun) (c : Noun → Outcome) : Prop :=
  ∀ S, D S → NockEval S f (c S)

/-- The data-jet contract of `c` restricted to `D`: the subject encoded by
    `encNoun`, the outcome by `encOut`. -/
def onContract (D : Noun → Prop) (c : Noun → Outcome) : Contract {S : Noun // D S} Outcome :=
  ⟨fun x => encNoun x.1, encOut, fun x => c x.1⟩

/-- **`jet_transport` on a domain.** -/
theorem jet_transport_on {D : Noun → Prop} {f : Noun} {c : Noun → Outcome}
    (hc : LeafOn D f c) : Implements (onContract D c) (jetT f) :=
  fun x => jet_step (hc x.1 x.2)

theorem onContract_respects (D : Noun → Prop) (c : Noun → Outcome) :
    (onContract D c).Respects :=
  respects_of_inj fun _ _ h => Subtype.ext (encNoun_inj h)

-- ---------------------------------------------------------------------------
-- The arm, its domain and its model
-- ---------------------------------------------------------------------------

/-- The `++dec` gate's battery formula, the computation under any hint:
    lean-nock's `decBat_guardBody`, written out. -/
def hoonDecBodyF : Noun :=
  n! "[6 [5 [1 0] 0 6] [0 0] 8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1]"

theorem hoonDecBodyF_eq : hoonDecBodyF = decBat_guardBody := rfl

/-- The subjects on which the arm has an outcome: everything but a core whose
    sample (axis 6) is a cell. -/
def HoonDecDom : Noun → Prop
  | cell _ (cell (cell _ _) _) => False
  | _ => True

/-- The model of the arm on the gate core: `dec` of the sample, crashing at
    zero and where there is no sample.  (On a cell sample, off the domain, the
    arm diverges; the value given there is never used.) -/
def hoonDecC : Noun → Outcome
  | cell _ (cell (atom (n + 1)) _) => .val (atom n)
  | _ => .exit

private theorem body_crash_noSix {S : Noun} (h : fasO (atom 6) S = none) :
    NockEval S hoonDecBodyF .exit :=
  NockEval.op6_crash (NockEval.op5_crashR NockEval.op1 (NockEval.op0_crash h))

/-- **The Hoon `++dec` leaf**: the arm meets `hoonDecC` on its domain, from
    lean-nock's battery-generic `dec_body_correct` and `dec_body_underflow`. -/
theorem hoon_dec_leaf : LeafOn HoonDecDom hoonDecBodyF hoonDecC
  | atom k, _ => body_crash_noSix (fasO_six_atom k)
  | cell _ (atom t), _ => body_crash_noSix (fasO_six_atomtail _ t)
  | cell B (cell (atom 0) ctx), _ => dec_body_underflow B ctx
  | cell B (cell (atom (n + 1)) ctx), _ => dec_body_correct B n ctx
  | cell _ (cell (cell _ _) _), h => h.elim

/-- Off the domain the arm diverges: lean-nock's `dec_body_cell_diverges`. -/
theorem hoon_dec_off_domain (S : Noun) (h : ¬ HoonDecDom S) : Nock.Diverges S hoonDecBodyF := by
  match S, h with
  | cell B (cell (cell x y) ctx), _ => exact dec_body_cell_diverges B x y ctx
  | atom _, h => exact absurd trivial h
  | cell _ (atom _), h => exact absurd trivial h
  | cell _ (cell (atom _) _), h => exact absurd trivial h

/-- Off the domain the compiled arm diverges too: there is nothing for a jet
    to return. -/
theorem hoon_dec_off_domain_term (S : Noun) (h : ¬ HoonDecDom S) :
    _root_.Diverges (nockToSki hoonDecBodyF ⬝ encNoun S) :=
  (embed_diverges (enc_encNoun S)).2 (hoon_dec_off_domain S h)

/-- **`++dec` transports**: the compiled arm, copied code-free, implements the
    Hoon `++dec` contract on its domain. -/
theorem hoon_dec_transport : Implements (onContract HoonDecDom hoonDecC) (jetT hoonDecBodyF) :=
  jet_transport_on hoon_dec_leaf

theorem hoonDecContract_respects : (onContract HoonDecDom hoonDecC).Respects :=
  onContract_respects HoonDecDom hoonDecC

-- ---------------------------------------------------------------------------
-- Registration is not computation: a hint with a constant clue
-- ---------------------------------------------------------------------------

/-- **Any constant-clue dynamic hint over the arm has the same contract.**
    The clue `[1 k]` produces a value on every subject, so the hint is
    transparent (lean-nock's `hint_dynamic_transparent`).  Neither the tag
    (`%mean`, `%fast`, …) nor the clue's content enters. -/
theorem hoon_dec_hinted_leaf (tag k : Noun) :
    LeafOn HoonDecDom
      (cell (atom 11) (cell (cell tag (cell (atom 1) k)) hoonDecBodyF)) hoonDecC :=
  fun S hS => (hint_dynamic_transparent tag (cell (atom 1) k) S hoonDecBodyF
    NockEval.op1 (hoonDecC S)).2 (hoon_dec_leaf S hS)

-- ---------------------------------------------------------------------------
-- The benchmark's program: `urbit/benchmark/desk/bar/dec.nock`
-- ---------------------------------------------------------------------------

/-- Arm 4 of the benchmark core: slam arm 5's gate with the subject,
    `[8 [9 5 0 1] 9 2 10 [6 0 7] 0 2]`. -/
def hoonDecBenchArm4 : Noun := n! "[8 [9 5 0 1] 9 2 10 [6 0 7] 0 2]"

/-- Arm 5 of the benchmark core: the gate `[body [0 core]]`,
    `[8 [1 0] [1 body] 0 1]`. -/
def hoonDecBenchArm5 : Noun :=
  cell (atom 8) (cell (cell (atom 1) (atom 0))
    (cell (cell (atom 1) hoonDecBodyF) (cell (atom 0) (atom 1))))

/-- The benchmark's formula, as `dec.nock` prints it (its subject
    `1.000.000` is the default; `tests.json` runs it at `100`). -/
def hoonDecBenchF : Noun :=
  n! "[8 [1 [8 [9 5 0 1] 9 2 10 [6 0 7] 0 2] 8 [1 0] [1 6 [5 [1 0] 0 6] [0 0] 8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1] 0 1] 9 4 0 1]"

/-- The benchmark's text, in parts: the core `[arm4 arm5]` pushed on the
    subject, arm 4 fired; arm 5's gate battery is the arm `hoonDecBodyF`. -/
theorem hoonDecBenchF_parts : hoonDecBenchF =
    cell (atom 8) (cell (cell (atom 1) (cell hoonDecBenchArm4 hoonDecBenchArm5))
      (cell (atom 9) (cell (atom 4) (cell (atom 0) (atom 1))))) := rfl

/-- **The benchmark program reduces to the arm**: on subject `a`, it runs the
    arm against the gate core `[body [a [[arm4 arm5] a]]]` (arm 5's gate
    `[body [0 core]]` with the sample `a` slammed in), for every
    outcome. -/
theorem hoon_dec_bench_call (a : Noun) {o : Outcome}
    (h : NockEval (cell hoonDecBodyF (cell a
      (cell (cell hoonDecBenchArm4 hoonDecBenchArm5) a))) hoonDecBodyF o) :
    NockEval a hoonDecBenchF o := by
  rw [hoonDecBenchF_parts]
  refine NockEval.op8 NockEval.op1 ?_
  refine NockEval.op9 (NockEval.op0 (fasO_one _)) (fasO_four _ _ _) ?_
  -- arm 4: [8 [9 5 0 1] [9 2 [10 [6 [0 7]] [0 2]]]]
  show NockEval _ (cell (atom 8) (cell
    (cell (atom 9) (cell (atom 5) (cell (atom 0) (atom 1))))
    (cell (atom 9) (cell (atom 2) (cell (atom 10) (cell
      (cell (atom 6) (cell (atom 0) (atom 7))) (cell (atom 0) (atom 2)))))))) o
  refine NockEval.op8 (r1 := cell hoonDecBodyF (cell (atom 0)
    (cell (cell hoonDecBenchArm4 hoonDecBenchArm5) a))) ?_ ?_
  · -- arm 5 builds the gate
    refine NockEval.op9 (NockEval.op0 (fasO_one _)) (fasO_five _ _ _) ?_
    exact NockEval.op8 NockEval.op1 (NockEval.autocons NockEval.op1 (NockEval.op0 (fasO_one _)))
  · refine NockEval.op9 ?_ (fasO_head _ _) h
    exact NockEval.op10 (NockEval.op0 (fasO_head _ _)) (NockEval.op0 (fasO_seven _ _ _))
      (haxO_six _ _ _ _)

/-- **The benchmark computes `dec`**: `*[n+1 hoonDecBenchF] = n`, for every
    `n`, from the leaf.  (`dec.nock` at its default subject `1.000.000` gives
    `999.999`; `tests.json` at `100` gives `99`.) -/
theorem hoon_dec_bench (n : Nat) : NockEval (atom (n + 1)) hoonDecBenchF (.val (atom n)) :=
  hoon_dec_bench_call _ (hoon_dec_leaf _ trivial)

/-- At `0` the benchmark crashes (the underflow guard). -/
theorem hoon_dec_bench_zero : NockEval (atom 0) hoonDecBenchF .exit :=
  hoon_dec_bench_call _ (hoon_dec_leaf _ trivial)

end Nock2Ski
