import Nock2Ski.PredSkel
import Nock2Ski.Probe
import Nock.Comp
import Nock.HoonOne

open Nock Nock.Noun
open Term

/-!
# The released programs, their products as lean-nock's theorems

`release/nock/programs.txt` and `release/nock/hidden/programs.txt` state
five Nock programs: the spec's count-up `dec` at 7 (`countup_dec_7`, and
over a hidden 8-bit atom `countup_hidden_7`), Hoon's `++dec` at 12 and at 0
(`hoon_dec_12`, `hoon_dec_0`, the gate pushed by `[1 …]` and called with a
literal sample; `hoon_dec_hidden_12` takes the sample from the hidden
subject), and Hoon's compiled `++add` over two hidden atoms
(`hoon_add_hidden_3_4`, `hoon_add_hidden_6_57`).  Each formula is written
out here as the released text (`n!`) and its product is proved from
lean-nock:

- `countUpF = countUp` by `rfl`, so `countUp_correct 6` is the run;
- Hoon's `++dec` from `urbit/benchmark` is **not** lean-nock's `decBat`: the
  guard and loop body are lean-nock's `decBat_guardBody` to the cell, but the
  `%fast` hint's clue formula differs (`hoonDecBat_parts`: the benchmark's
  is the constant `[1 [[1 %dec] [[7 …] [0 1]]]]`, lean-nock's `decBat_hintF`
  the autocons `[[1 [[1 %dec] [7 …]]] [0 1]]`), and lean-nock's `dec_correct`
  and `dec_loop_inv` are stated on `decBat` itself (`decLoopCore` carries
  it), so they do not compose into the released formulas.  The three
  Hoon `dec` runs are therefore lean-nock's fuel interpreter evaluated by
  the kernel: `nockF_sound` on `decide +kernel` (`hoonDecHidden_eval`,
  `hoonDec12_eval`, `hoonDec0_crash`; a few hundred Nock steps each);
- Hoon's `++add` from `urbit/benchmark` is not lean-nock's `addBat` either
  (it finds `dec` at `[9 10 0 7]` where lean-nock's finds it at `[9 2398 [0
  8191]]`), so `add_correct` does not apply; its two runs are the same
  kernel evaluation (`hoonAdd_3_4`, `hoonAdd_6_57`).

With them the released statements' completeness is unconditional: the
hidden-subject verifiers accept the witness bits (`countup_hidden_7_complete`,
`hoon_dec_hidden_12_complete`, `hoon_add_hidden_3_4_complete`,
`hoon_add_hidden_6_57_complete`, by `nock_pred_complete` and
`nock_pred2_complete`), and the public rows' terms reach the products'
code-free encodings, which the probe tables read (`countup_dec_7_probe`,
`hoon_dec_12_probe`, by `probe_complete_nock`), and the crash row's term
reaches `Err` (`hoon_dec_0_crash`, by `shared_crash`).

This module imports `Nock.Comp` and `Nock.HoonOne` beside lean-ski, which
lean-nock's `namespace Nock` (its branch `namespace-nock`) made possible;
before it `Nock.Comp` reached `Nock.Fuel`, whose root-level `Diverges`
clashed with `Ski.Basic`'s, and these runs were cited in prose.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- The count-up `dec`: `countup_dec_7`, `countup_hidden_7`
-- ---------------------------------------------------------------------------

/-- The released formula of `countup_dec_7` and `countup_hidden_7`. -/
def countUpF : Noun :=
  n! "[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]"

/-- The released text is lean-nock's `countUp`. -/
theorem countUpF_eq : countUpF = countUp := rfl

/-- `*[7 countUpF] = 6`, lean-nock's `countUp_correct`. -/
theorem countUp_7 : NockEval (.atom 7) countUpF (.val (.atom 6)) := by
  rw [countUpF_eq]; exact countUp_correct 6

/-- **`countup_hidden_7` is complete**: the verifier accepts the 8 bits of 7
    for the product 6. -/
theorem countup_hidden_7_complete :
    Eval (nockPredV countUpF 8 ⬝ encNoun (.atom 6) ⬝ boolsT (bitsK 8 7)) K :=
  nock_pred_complete (by decide) (by decide) countUp_7

/-- **`countup_dec_7`'s probe table is makeable**: the row's term reaches
    `encNoun 6`, the tree `nounV 6` reads (`probe_complete`). -/
theorem countup_dec_7_probe : WSteps (compiled countUpF (.atom 7)) (encNoun (.atom 6)) :=
  probe_complete_nock countUp_7

-- ---------------------------------------------------------------------------
-- Hoon's `++dec`: `hoon_dec_12`, `hoon_dec_0`, `hoon_dec_hidden_12`
-- ---------------------------------------------------------------------------

/-- The `%fast` hint's clue formula of the benchmark's `++dec` battery. -/
def hoonDecClue : Noun :=
  n! "[1 [1 1717658988] [7 [[0 1] [8 [1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 2 [0 1]]]]] [0 1]]"

/-- The benchmark's `++dec` battery: lean-nock's guard and loop
    (`decBat_guardBody`) under a `%fast` hint with `hoonDecClue`. -/
def hoonDecBat : Noun :=
  cell (atom 11) (cell (cell (atom 1851876717) hoonDecClue) decBat_guardBody)

/-- The gate the released formulas push: the battery with sample 0 and
    context 0. -/
def hoonDecGate : Noun := cell hoonDecBat (cell (atom 0) (atom 0))

/-- The released formula of `hoon_dec_hidden_12`: push the gate, then fire
    arm 2 of the gate with the subject as its sample,
    `[8 [1 gate] [9 2 [10 [6 [0 3]] [0 2]]]]`. -/
def hoonDecHiddenF : Noun :=
  n! "[8 [1 [[11 [1851876717 [1 [1 1717658988] [7 [[0 1] [8 [1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 2 [0 1]]]]] [0 1]]] [6 [5 [1 0] [0 6]] [0 0] [8 [1 0] [8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 [10 [6 4 0 6] 0 1]] [9 2 0 1]]]]] 0 0]] [9 2 [10 [6 [0 3]] [0 2]]]]"

/-- The released text, in parts: the gate is `hoonDecGate`. -/
theorem hoonDecHiddenF_parts : hoonDecHiddenF =
    cell (atom 8) (cell (cell (atom 1) hoonDecGate)
      (cell (atom 9) (cell (atom 2) (cell (atom 10)
        (cell (cell (atom 6) (cell (atom 0) (atom 3))) (cell (atom 0) (atom 2))))))) := rfl

/-- The benchmark's battery against lean-nock's: the same guard body, a
    different clue (`decBat = [11 [%fast decBat_hintF] decBat_guardBody]`,
    `decBat_parts` in lean-nock). -/
theorem hoonDecBat_parts :
    hoonDecBat = cell (atom 11) (cell (cell (atom 1851876717) hoonDecClue) decBat_guardBody) ∧
    hoonDecClue ≠ decBat_hintF := ⟨rfl, by decide⟩

/-- `*[12 hoonDecHiddenF] = 11`: lean-nock's fuel interpreter, run by the
    kernel, and `nockF_sound`. -/
theorem hoonDecHidden_eval : NockEval (.atom 12) hoonDecHiddenF (.val (.atom 11)) :=
  nockF_sound 4000 (by decide +kernel)

/-- **`hoon_dec_hidden_12` is complete**: the verifier accepts the 8 bits of
    12 for the product 11. -/
theorem hoon_dec_hidden_12_complete :
    Eval (nockPredV hoonDecHiddenF 8 ⬝ encNoun (.atom 11) ⬝ boolsT (bitsK 8 12)) K :=
  nock_pred_complete (by decide) (by decide) hoonDecHidden_eval

/-- The released formula of `hoon_dec_12` and `hoon_dec_0` at sample `s`:
    `[7 [1 gate] [9 2 [10 [6 [1 s]] [0 1]]]]`, on subject 0. -/
def hoonDecF (s : Nat) : Noun :=
  cell (atom 7) (cell (cell (atom 1) hoonDecGate)
    (cell (atom 9) (cell (atom 2) (cell (atom 10)
      (cell (cell (atom 6) (cell (atom 1) (atom s))) (cell (atom 0) (atom 1)))))))

theorem hoonDecF_12 : hoonDecF 12 =
    n! "[7 [1 [[11 [1851876717 [1 [1 1717658988] [7 [[0 1] [8 [1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 2 [0 1]]]]] [0 1]]] [6 [5 [1 0] [0 6]] [0 0] [8 [1 0] [8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 [10 [6 4 0 6] 0 1]] [9 2 0 1]]]]] 0 0]] [9 2 [10 [6 [1 12]] [0 1]]]]" := rfl

theorem hoonDecF_0 : hoonDecF 0 =
    n! "[7 [1 [[11 [1851876717 [1 [1 1717658988] [7 [[0 1] [8 [1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 2 [0 1]]]]] [0 1]]] [6 [5 [1 0] [0 6]] [0 0] [8 [1 0] [8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 [10 [6 4 0 6] 0 1]] [9 2 0 1]]]]] 0 0]] [9 2 [10 [6 [1 0]] [0 1]]]]" := rfl

/-- `*[0 hoonDecF 12] = 11`, by the kernel. -/
theorem hoonDec12_eval : NockEval (.atom 0) (hoonDecF 12) (.val (.atom 11)) :=
  nockF_sound 4000 (by decide +kernel)

/-- `*[0 hoonDecF 0]` crashes (the underflow guard), by the kernel. -/
theorem hoonDec0_crash : NockEval (.atom 0) (hoonDecF 0) .exit :=
  nockF_sound 4000 (by decide +kernel)

/-- **`hoon_dec_12`'s probe table is makeable**: the shared row's term
    reaches `encNoun 11`. -/
theorem hoon_dec_12_probe : WSteps (share (compiled (hoonDecF 12) (.atom 0))) (encNoun (.atom 11)) :=
  probe_complete_nock_shared hoonDec12_eval

/-- **`hoon_dec_0` crashes**: the shared row's term reaches `Err`. -/
theorem hoon_dec_0_crash : WSteps (share (compiled (hoonDecF 0) (.atom 0))) errT :=
  shared_crash hoonDec0_crash

-- ---------------------------------------------------------------------------
-- Hoon's `++add`: `hoon_add_hidden_3_4`, `hoon_add_hidden_6_57`
-- ---------------------------------------------------------------------------

/-- The released formula of the `hoon_add_hidden_*` statements,
    `urbit/benchmark/desk/bar/add.nock`, on the hidden subject `[a b]`. -/
def hoonAddF : Noun :=
  n! "[8 [1 [8 [1 0 0] [1 6 [5 [1 0] 0 12] [0 13] 9 2 10 [6 [8 [9 10 0 7] 9 2 10 [6 0 28] 0 2] 4 0 13] 0 1] 0 1] [8 [1 0] [1 6 [5 [1 0] 0 6] [0 0] 8 [1 0] 8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1] 9 2 0 1] 0 1] 8 [9 4 0 1] 9 2 10 [6 [0 14] 0 15] 0 2] 9 11 0 1]"

/-- `*[[3 4] hoonAddF] = 7`: lean-nock's fuel interpreter, run by the kernel. -/
theorem hoonAdd_3_4 : NockEval (.cell (.atom 3) (.atom 4)) hoonAddF (.val (.atom 7)) :=
  nockF_sound 4000 (by decide +kernel)

/-- `*[[6 57] hoonAddF] = 63`. -/
theorem hoonAdd_6_57 : NockEval (.cell (.atom 6) (.atom 57)) hoonAddF (.val (.atom 63)) :=
  nockF_sound 4000 (by decide +kernel)

/-- **`hoon_add_hidden_3_4` is complete**: the verifier accepts the bits of
    `[3 4]` at 4 bits each for the product 7. -/
theorem hoon_add_hidden_3_4_complete :
    Eval (nockPred2V hoonAddF 4 ⬝ encNoun (.atom 7) ⬝ boolsT (bitsK 4 3 ++ bitsK 4 4)) K :=
  nock_pred2_complete (by decide) (by decide) (by decide) hoonAdd_3_4

/-- **`hoon_add_hidden_6_57` is complete**: `[6 57]` at 6 bits each, product 63. -/
theorem hoon_add_hidden_6_57_complete :
    Eval (nockPred2V hoonAddF 6 ⬝ encNoun (.atom 63) ⬝ boolsT (bitsK 6 6 ++ bitsK 6 57)) K :=
  nock_pred2_complete (by decide) (by decide) (by decide) hoonAdd_6_57

end Nock2Ski
