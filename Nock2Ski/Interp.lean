import Nock2Ski.InterpRuns

open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

set_option linter.unusedSimpArgs false

/-!
# The interpreter fallback, read from the compiler's own terms

Milestone M3 of `PLAN.md`: `nock.ski`'s interpreter `nockI` and its
helpers (`nockP`, `nockO`, `autocons`, `appI`, `cel2`, `decop…`, `revb`,
`tlb`, `path`, `descend`, `slotB`, `editP`, `editB`), the compiler's
default for opcode 12 (`op12`), and `app`, which now falls back to `nockI`
on a plain `Cell`, as closed SKI terms **identical to the terms SKIjack
emits**, with their specifications.

## The terms, and how they are pinned

The file was restructured so that `nockI` is its only recursive equation:
the helpers take the evaluator as a parameter `ev`, `appI` re-enters
through `ev`, and `nockO` never names `nockI`.  lean-ski's front end ties
self-recursion but not mutual recursion, and with the cycle gone
`Front.compileDecls` accepts the file (`Decls.lean`: the parse is pinned
once, `parse_pin`, and everything is stated over `nockFileD`).

Each equation's term `xT` is **defined as the file's term** (`termD`,
`InterpDefs.lean`), so its pin to `Front.termOf nockFile` is `termD_pin`
(`InterpPins.lean`, `InterpPinsE.lean`).  What the proofs need is the
term's *structure*: `x_eq : xT = toTerm (absNF params body)` (or `Ycomb ⬝
xG` for `nockI`, `revb`, `descend`, `editP`), checked by `decide +kernel`
(`InterpEq.lean`, `InterpEqI.lean`).  Those bodies are written as
`skijack` lifts them (`Ski/Compile.lean`'s `comp`): every λ-chain is its
own closed combinator over the binders it captures (in scope order) and
its own parameters, named `xK0, xK1, …`, and the use site is that
combinator applied to the captured binders.  Stating the structure this
way, with the dependencies as closed terms, lets the kernel evaluate each
equation's chain of dependencies once, shared between the two sides of
`x_eq`; the parse is pinned once (`Decls.lean`), and the kernel-heavy
theorems are spread over a chain of modules so that each `lean` process
stays within about 4 GB.

β for each combinator (`xK3_beta`, `nockOT_beta`, …) is lean-ski's
`absN_beta_close` through `absNF`, the closing computed by `simp` with
the propositional `close_app`/`close_var`/`close_toO` (unfolding
`OTerm.close` definitionally would make the kernel evaluate every constant
in the term).  The twelve M1 terms (`hdT`, …, `ifnT`) are unchanged and
still pinned in `Prims.lean`; `app` moved here because it names `nockI`.
Here: β for the equations' terms, `nockO` on each opcode tag
(`nockO_O2 : nockO ev O2 s t ↠ cel2 t (…)`), and the pure specifications.

## The specifications

Pure ones here, over `Enc` in `InterpEnc.lean`: `decop_spec` reads an
opcode's canonical bits to its tag (`Obad` from 13 on); `revb`, `tlb` and
`path` turn an axis's bits into `axisPath` (`path_spec`); `descend` is the
`hd`/`tl` chain `pickT` (`descend_spec`), so `slotB` is the tagged pull
(`slotB_pos`); `app_cell` is the fallback: `app (Cell h t) x ↠ nockI x
(Cell h t)`.
-/

namespace Nock2Ski

theorem decop11T_beta (x0 : Term) :
    WSteps (decop11T ⬝ x0) ((x0 ⬝ (opC 3)) ⬝ decop11K3) := by
  rw [decop11_eq]
  have h := absNF_beta_close [0] (((.var 0) ⬝ₒ (opC 3).toO) ⬝ₒ decop11K3.toO) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop01T_beta (x0 : Term) :
    WSteps (decop01T ⬝ x0) ((x0 ⬝ (opC 13)) ⬝ decop01K3) := by
  rw [decop01_eq]
  have h := absNF_beta_close [0] (((.var 0) ⬝ₒ (opC 13).toO) ⬝ₒ decop01K3.toO) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop10T_beta (x0 : Term) :
    WSteps (decop10T ⬝ x0) ((x0 ⬝ (opC 2)) ⬝ decop10K3) := by
  rw [decop10_eq]
  have h := absNF_beta_close [0] (((.var 0) ⬝ₒ (opC 2).toO) ⬝ₒ decop10K3.toO) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop00T_beta (x0 : Term) :
    WSteps (decop00T ⬝ x0) ((x0 ⬝ (opC 13)) ⬝ decop00K4) := by
  rw [decop00_eq]
  have h := absNF_beta_close [0] (((.var 0) ⬝ₒ (opC 13).toO) ⬝ₒ decop00K4.toO) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem tlbT_beta (x0 : Term) :
    WSteps (tlbT ⬝ x0) ((x0 ⬝ NilC) ⬝ tlbK0) := by
  rw [tlb_eq]
  have h := absNF_beta_close [0] (((.var 0) ⬝ₒ NilC.toO) ⬝ₒ tlbK0.toO) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem pathT_beta (x0 : Term) :
    WSteps (pathT ⬝ x0) (tlbT ⬝ ((revbT ⬝ x0) ⬝ NilC)) := by
  rw [path_eq]
  have h := absNF_beta_close [0] (tlbT.toO ⬝ₒ ((revbT.toO ⬝ₒ (.var 0)) ⬝ₒ NilC.toO)) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem slotBT_beta (x0 x1 : Term) :
    WSteps (slotBT ⬝ x0 ⬝ x1) ((x0 ⬝ ErrC) ⬝ (slotBK0 ⬝ x1)) := by
  rw [slotB_eq]
  have h := absNF_beta_close [0, 1] (((.var 0) ⬝ₒ ErrC.toO) ⬝ₒ (slotBK0.toO ⬝ₒ .var 1)) (fun _ => K) [x0, x1] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem editBT_beta (x0 x1 x2 : Term) :
    WSteps (editBT ⬝ x0 ⬝ x1 ⬝ x2) ((x0 ⬝ ErrC) ⬝ ((editBK0 ⬝ x1) ⬝ x2)) := by
  rw [editB_eq]
  have h := absNF_beta_close [0, 1, 2] (((.var 0) ⬝ₒ ErrC.toO) ⬝ₒ ((editBK0.toO ⬝ₒ .var 1) ⬝ₒ .var 2)) (fun _ => K) [x0, x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem autoconsT_beta (x0 x1 x2 x3 : Term) :
    WSteps (autoconsT ⬝ x0 ⬝ x1 ⬝ x2 ⬝ x3) ((forceT ⬝ ((x0 ⬝ x1) ⬝ x2)) ⬝ (((autoconsK1 ⬝ x0) ⬝ x1) ⬝ x3)) := by
  rw [autocons_eq]
  have h := absNF_beta_close [0, 1, 2, 3] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 1)) ⬝ₒ (.var 2))) ⬝ₒ (((autoconsK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 3)) (fun _ => K) [x0, x1, x2, x3] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appIT_beta (x0 x1 x2 : Term) :
    WSteps (appIT ⬝ x0 ⬝ x1 ⬝ x2) ((((x1 ⬝ appIK0) ⬝ (((appIK1 ⬝ x0) ⬝ x1) ⬝ x2)) ⬝ (appIK2 ⬝ x2)) ⬝ ErrC) := by
  rw [appI_eq]
  have h := absNF_beta_close [0, 1, 2] (((((.var 1) ⬝ₒ appIK0.toO) ⬝ₒ (((appIK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 2)) ⬝ₒ (appIK2.toO ⬝ₒ .var 2)) ⬝ₒ ErrC.toO) (fun _ => K) [x0, x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem cel2T_beta (x0 x1 : Term) :
    WSteps (cel2T ⬝ x0 ⬝ x1) ((((x0 ⬝ cel2K0) ⬝ (cel2K1 ⬝ x1)) ⬝ (cel2K2 ⬝ x1)) ⬝ ErrC) := by
  rw [cel2_eq]
  have h := absNF_beta_close [0, 1] (((((.var 0) ⬝ₒ cel2K0.toO) ⬝ₒ (cel2K1.toO ⬝ₒ .var 1)) ⬝ₒ (cel2K2.toO ⬝ₒ .var 1)) ⬝ₒ ErrC.toO) (fun _ => K) [x0, x1] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem op12T_beta (x0 x1 x2 : Term) :
    WSteps (op12T ⬝ x0 ⬝ x1 ⬝ x2) ErrC := by
  rw [op12_eq]
  have h := absNF_beta_close [0, 1, 2] ErrC.toO (fun _ => K) [x0, x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop1T_beta (x0 : Term) :
    WSteps (decop1T ⬝ x0) ((x0 ⬝ (opC 1)) ⬝ decop1K0) := by
  rw [decop1_eq]
  have h := absNF_beta_close [0] (((.var 0) ⬝ₒ (opC 1).toO) ⬝ₒ decop1K0.toO) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop0T_beta (x0 : Term) :
    WSteps (decop0T ⬝ x0) ((x0 ⬝ (opC 13)) ⬝ decop0K0) := by
  rw [decop0_eq]
  have h := absNF_beta_close [0] (((.var 0) ⬝ₒ (opC 13).toO) ⬝ₒ decop0K0.toO) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOT_beta (x0 x1 x2 x3 : Term) :
    WSteps (nockOT ⬝ x0 ⬝ x1 ⬝ x2 ⬝ x3) ((((((((((((((x1 ⬝ ((((x3 ⬝ (nockOK0 ⬝ x2)) ⬝ nockOK1) ⬝ nockOK2) ⬝ ErrC)) ⬝ x3) ⬝ ((cel2T ⬝ x3) ⬝ ((nockOK5 ⬝ x0) ⬝ x2))) ⬝ (celT ⬝ ((x0 ⬝ x2) ⬝ x3))) ⬝ (incT ⬝ ((x0 ⬝ x2) ⬝ x3))) ⬝ ((cel2T ⬝ x3) ⬝ ((nockOK8 ⬝ x0) ⬝ x2))) ⬝ ((cel2T ⬝ x3) ⬝ ((nockOK10 ⬝ x0) ⬝ x2))) ⬝ ((cel2T ⬝ x3) ⬝ ((nockOK12 ⬝ x0) ⬝ x2))) ⬝ ((cel2T ⬝ x3) ⬝ ((nockOK14 ⬝ x0) ⬝ x2))) ⬝ ((cel2T ⬝ x3) ⬝ ((nockOK19 ⬝ x0) ⬝ x2))) ⬝ ((cel2T ⬝ x3) ⬝ ((nockOK26 ⬝ x0) ⬝ x2))) ⬝ ((cel2T ⬝ x3) ⬝ ((nockOK32 ⬝ x0) ⬝ x2))) ⬝ (((op12T ⬝ x0) ⬝ x2) ⬝ x3)) ⬝ ErrC) := by
  rw [nockO_eq]
  have h := absNF_beta_close [0, 1, 2, 3] (((((((((((((((.var 1) ⬝ₒ (((((.var 3) ⬝ₒ (nockOK0.toO ⬝ₒ .var 2)) ⬝ₒ nockOK1.toO) ⬝ₒ nockOK2.toO) ⬝ₒ ErrC.toO)) ⬝ₒ (.var 3)) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK5.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ (celT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 3)))) ⬝ₒ (incT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 3)))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK8.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK10.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK12.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK14.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK19.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK26.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK32.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ (((op12T.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 2)) ⬝ₒ (.var 3))) ⬝ₒ ErrC.toO) (fun _ => K) [x0, x1, x2, x3] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decopT_beta (x0 : Term) :
    WSteps (decopT ⬝ x0) ((x0 ⬝ (opC 0)) ⬝ decopK0) := by
  rw [decop_eq]
  have h := absNF_beta_close [0] (((.var 0) ⬝ₒ (opC 0).toO) ⬝ₒ decopK0.toO) (fun _ => K) [x0] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockPT_beta (x0 x1 x2 x3 : Term) :
    WSteps (nockPT ⬝ x0 ⬝ x1 ⬝ x2 ⬝ x3) ((((x2 ⬝ (((nockPK0 ⬝ x0) ⬝ x1) ⬝ x3)) ⬝ ((((nockPK1 ⬝ x0) ⬝ x1) ⬝ x2) ⬝ x3)) ⬝ ((((nockPK2 ⬝ x0) ⬝ x1) ⬝ x2) ⬝ x3)) ⬝ ErrC) := by
  rw [nockP_eq]
  have h := absNF_beta_close [0, 1, 2, 3] (((((.var 2) ⬝ₒ (((nockPK0.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 3)) ⬝ₒ ((((nockPK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 2) ⬝ₒ .var 3)) ⬝ₒ ((((nockPK2.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 2) ⬝ₒ .var 3)) ⬝ₒ ErrC.toO) (fun _ => K) [x0, x1, x2, x3] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appT_beta (x0 x1 : Term) :
    WSteps (appT ⬝ x0 ⬝ x1) ((((x0 ⬝ appK0) ⬝ ((appK1 ⬝ x0) ⬝ x1)) ⬝ (appK2 ⬝ x1)) ⬝ ErrC) := by
  rw [app_eq]
  have h := absNF_beta_close [0, 1] (((((.var 0) ⬝ₒ appK0.toO) ⬝ₒ ((appK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1)) ⬝ₒ (appK2.toO ⬝ₒ .var 1)) ⬝ₒ ErrC.toO) (fun _ => K) [x0, x1] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h


/-- `nockO ev o s t` on each opcode tag: the branch, with `ev`, `s`, `t` in place. -/
theorem nockO_O0 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 0 ⬝ s ⬝ t) ((((t ⬝ (nockOK0 ⬝ s)) ⬝ nockOK1) ⬝ nockOK2) ⬝ ErrC) :=
  (nockOT_beta ev (opC 0) s t).trans (opC_sel0 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O1 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 1 ⬝ s ⬝ t) t :=
  (nockOT_beta ev (opC 1) s t).trans (opC_sel1 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O2 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 2 ⬝ s ⬝ t) ((cel2T ⬝ t) ⬝ ((nockOK5 ⬝ ev) ⬝ s)) :=
  (nockOT_beta ev (opC 2) s t).trans (opC_sel2 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O3 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 3 ⬝ s ⬝ t) (celT ⬝ ((ev ⬝ s) ⬝ t)) :=
  (nockOT_beta ev (opC 3) s t).trans (opC_sel3 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O4 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 4 ⬝ s ⬝ t) (incT ⬝ ((ev ⬝ s) ⬝ t)) :=
  (nockOT_beta ev (opC 4) s t).trans (opC_sel4 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O5 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 5 ⬝ s ⬝ t) ((cel2T ⬝ t) ⬝ ((nockOK8 ⬝ ev) ⬝ s)) :=
  (nockOT_beta ev (opC 5) s t).trans (opC_sel5 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O6 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 6 ⬝ s ⬝ t) ((cel2T ⬝ t) ⬝ ((nockOK10 ⬝ ev) ⬝ s)) :=
  (nockOT_beta ev (opC 6) s t).trans (opC_sel6 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O7 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 7 ⬝ s ⬝ t) ((cel2T ⬝ t) ⬝ ((nockOK12 ⬝ ev) ⬝ s)) :=
  (nockOT_beta ev (opC 7) s t).trans (opC_sel7 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O8 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 8 ⬝ s ⬝ t) ((cel2T ⬝ t) ⬝ ((nockOK14 ⬝ ev) ⬝ s)) :=
  (nockOT_beta ev (opC 8) s t).trans (opC_sel8 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O9 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 9 ⬝ s ⬝ t) ((cel2T ⬝ t) ⬝ ((nockOK19 ⬝ ev) ⬝ s)) :=
  (nockOT_beta ev (opC 9) s t).trans (opC_sel9 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O10 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 10 ⬝ s ⬝ t) ((cel2T ⬝ t) ⬝ ((nockOK26 ⬝ ev) ⬝ s)) :=
  (nockOT_beta ev (opC 10) s t).trans (opC_sel10 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O11 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 11 ⬝ s ⬝ t) ((cel2T ⬝ t) ⬝ ((nockOK32 ⬝ ev) ⬝ s)) :=
  (nockOT_beta ev (opC 11) s t).trans (opC_sel11 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_O12 (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 12 ⬝ s ⬝ t) (((op12T ⬝ ev) ⬝ s) ⬝ t) :=
  (nockOT_beta ev (opC 12) s t).trans (opC_sel12 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem nockO_Obad (ev s t : Term) : WSteps (nockOT ⬝ ev ⬝ opC 13 ⬝ s ⬝ t) ErrC :=
  (nockOT_beta ev (opC 13) s t).trans (opC_sel13 _ _ _ _ _ _ _ _ _ _ _ _ _ _)

-- ---------------------------------------------------------------------------
-- Axes
-- ---------------------------------------------------------------------------

/-- The binary digits of an axis below its leading one, `false` the head
    and `true` the tail, by recursion: `axisPath (2a + b) = axisPath a ++ [b]`
    for `a ≥ 1`.  Equal to `Front.axisSteps` (`axisPath_eq_axisSteps`). -/
def axisPath : Nat → List Bool
  | 0 => []
  | 1 => []
  | n + 2 => axisPath ((n + 2) / 2) ++ [(n + 2) % 2 == 1]
termination_by n => n
decreasing_by omega

theorem axisPath_zero : axisPath 0 = [] := by simp [axisPath]
theorem axisPath_one : axisPath 1 = [] := by simp [axisPath]
theorem axisPath_rec {n : Nat} (h : 2 ≤ n) : axisPath n = axisPath (n / 2) ++ [n % 2 == 1] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [axisPath]

-- `axisPath` and `Front.axisSteps` agree: `Nat.toDigits 2` peels the least
-- significant digit last.
section AxisSteps

private theorem toDigitsCore_app :
    ∀ (fuel n : Nat) (ds : List Char),
      Nat.toDigitsCore 2 fuel n ds = Nat.toDigitsCore 2 fuel n [] ++ ds
  | 0, _, _ => rfl
  | fuel + 1, n, ds => by
    simp only [Nat.toDigitsCore]
    split
    · rfl
    · rw [toDigitsCore_app fuel (n / 2) [Nat.digitChar (n % 2)],
        toDigitsCore_app fuel (n / 2) (Nat.digitChar (n % 2) :: ds), List.append_assoc]
      rfl

private theorem toDigitsCore_fuel :
    ∀ (f₁ f₂ n : Nat) (ds : List Char), n < f₁ → n < f₂ →
      Nat.toDigitsCore 2 f₁ n ds = Nat.toDigitsCore 2 f₂ n ds
  | f₁ + 1, f₂ + 1, n, ds, h₁, h₂ => by
    simp only [Nat.toDigitsCore]
    split
    · rfl
    · rename_i hn
      exact toDigitsCore_fuel f₁ f₂ (n / 2) _ (by omega) (by omega)

private theorem toDigits_rec {n : Nat} (h : 2 ≤ n) :
    Nat.toDigits 2 n = Nat.toDigits 2 (n / 2) ++ [Nat.digitChar (n % 2)] := by
  unfold Nat.toDigits
  conv => lhs; rw [Nat.toDigitsCore]
  have hne : ¬ n / 2 = 0 := by omega
  simp only [hne, ↓reduceIte]
  rw [toDigitsCore_app n (n / 2),
    toDigitsCore_fuel n (n / 2 + 1) (n / 2) [] (by omega) (by omega)]

private theorem toDigits_ne_nil (n : Nat) : Nat.toDigits 2 n ≠ [] := by
  unfold Nat.toDigits Nat.toDigitsCore
  dsimp only
  split
  · simp
  · rw [toDigitsCore_app]; simp

theorem axisSteps_zero : Front.axisSteps 0 = [] := by decide
theorem axisSteps_one : Front.axisSteps 1 = [] := by decide

theorem axisSteps_rec {n : Nat} (h : 2 ≤ n) :
    Front.axisSteps n = Front.axisSteps (n / 2) ++ [n % 2 == 1] := by
  unfold Front.axisSteps
  rw [toDigits_rec h]
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, Nat.toDigits 2 (n / 2) = c :: cs := by
    cases hd : Nat.toDigits 2 (n / 2) with
    | nil => exact absurd hd (toDigits_ne_nil (n / 2))
    | cons c cs => exact ⟨c, cs, rfl⟩
  rw [hcs]
  simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.map_append,
    List.map_cons, List.map_nil]
  congr 2
  have : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases this with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

theorem axisPath_eq_axisSteps : ∀ n, axisPath n = Front.axisSteps n
  | 0 => by rw [axisPath_zero, axisSteps_zero]
  | 1 => by rw [axisPath_one, axisSteps_one]
  | n + 2 => by
    rw [axisPath_rec (by omega), axisSteps_rec (by omega),
      axisPath_eq_axisSteps ((n + 2) / 2)]
termination_by n => n
decreasing_by omega

end AxisSteps

-- ---------------------------------------------------------------------------
-- revb, tlb, path: an axis's bits to `axisPath`
-- ---------------------------------------------------------------------------

/-- **`revb`** reverses onto its accumulator. -/
theorem revb_spec : ∀ (bs acc : List Bool),
    WSteps (revbFix ⬝ bitsT bs ⬝ bitsT acc) (bitsT (bs.reverse ++ acc))
  | [], acc =>
    (WSteps.left _ (WSteps.left _ revb_unfold)).trans ((revbG_beta _ _ _).trans (nilT_elim _ _))
  | b :: bs, acc => by
    rw [show (b :: bs).reverse ++ acc = bs.reverse ++ (b :: acc) by simp]
    exact (WSteps.left _ (WSteps.left _ revb_unfold)).trans ((revbG_beta _ _ _).trans
      ((consT_elim _ _ _ _).trans ((revbK0_beta _ _ _ _).trans
        ((WSteps.right _ (ConsC_red _ _)).trans (revb_spec bs (b :: acc))))))

/-- **`tlb`** drops the first bit. -/
theorem tlb_cons (b : Bool) (bs : List Bool) : WSteps (tlbT ⬝ bitsT (b :: bs)) (bitsT bs) :=
  (tlbT_beta _).trans ((consT_elim _ _ _ _).trans (tlbK0_beta _ _))

/-- The canonical bits of `n ≥ 1`, most significant first, are a leading
    `true` and then `axisPath n`. -/
theorem bits_reverse : ∀ (n : Nat), 1 ≤ n → (bits n).reverse = true :: axisPath n
  | 0, h => absurd h (by omega)
  | 1, _ => by rw [bits_one, axisPath_one]; rfl
  | n + 2, _ => by
    rw [bits_pos (by omega), List.reverse_cons, bits_reverse ((n + 2) / 2) (by omega),
      axisPath_rec (n := n + 2) (by omega), List.cons_append]
  termination_by n => n

/-- **`path`** turns an axis's bits into `axisPath`. -/
theorem path_spec (n : Nat) (h : 1 ≤ n) : WSteps (pathT ⬝ bitsT (bits n)) (bitsT (axisPath n)) := by
  have e2 : WSteps (revbT ⬝ bitsT (bits n) ⬝ NilC) (bitsT ((bits n).reverse ++ [])) :=
    (WSteps.left _ (WSteps.left _ revbT_fix)).trans (revb_spec (bits n) [])
  rw [List.append_nil, bits_reverse n h] at e2
  exact (pathT_beta _).trans ((WSteps.right _ e2).trans (tlb_cons _ _))

-- ---------------------------------------------------------------------------
-- descend and slotB: the tagged pull, dynamically
-- ---------------------------------------------------------------------------

/-- **`descend`** builds the `hd`/`tl` chain `pickT`, lazily: the noun is
    never forced. -/
theorem descend_spec : ∀ (bs : List Bool) (e : Term), WSteps (descendFix ⬝ bitsT bs ⬝ e) (pickT e bs)
  | [], e =>
    (WSteps.left _ (WSteps.left _ descend_unfold)).trans ((descendG_beta _ _ _).trans (nilT_elim _ _))
  | b :: bs, e => by
    refine (WSteps.left _ (WSteps.left _ descend_unfold)).trans ((descendG_beta _ _ _).trans
      ((consT_elim _ _ _ _).trans ((descendK0_beta _ _ _ _).trans
        ((Compose.boolT_sel b _ _).trans ?_))))
    cases b
    · exact descend_spec bs (hdT ⬝ e)
    · exact descend_spec bs (tlT ⬝ e)

/-- **`slotB`** at axis `0` is a crash. -/
theorem slotB_zero (e : Term) : WSteps (slotBT ⬝ bitsT (bits 0) ⬝ e) errT := by
  rw [bits_zero]
  exact (slotBT_beta _ _).trans (nilT_elim _ _)

/-- **`slotB`** at axis `n ≥ 1` is the tagged pull along `axisPath n`. -/
theorem slotB_pos (n : Nat) (h : 1 ≤ n) (e : Term) :
    WSteps (slotBT ⬝ bitsT (bits n) ⬝ e) (pickT e (axisPath n)) := by
  have hb := bits_pos h
  rw [hb]
  refine (slotBT_beta _ _).trans ((consT_elim _ _ _ _).trans ((slotBK0_beta _ _ _).trans ?_))
  have e1 : WSteps (ConsC ⬝ boolT (n % 2 == 1) ⬝ bitsT (bits (n / 2))) (bitsT (bits n)) := by
    rw [hb]; exact ConsC_red _ _
  refine (WSteps.left _ (WSteps.right _ ((WSteps.right _ e1).trans (path_spec n h)))).trans ?_
  exact (WSteps.left _ (WSteps.left _ descendT_fix)).trans (descend_spec _ _)

-- ---------------------------------------------------------------------------
-- app: a formula applied to a subject
-- ---------------------------------------------------------------------------

/-- **`app`** crashes on an atom. -/
theorem app_atom (b x : Term) : WSteps (appT ⬝ atomT b ⬝ x) errT :=
  (appT_beta _ _).trans ((atomT_elim _ _ _ _ _).trans (appK0_beta _))

/-- **`app`** on a plain cell is the interpreter: `nockI x (Cell h t)`. -/
theorem app_cell (h t x : Term) : WSteps (appT ⬝ cellT h t ⬝ x) (nockIT ⬝ x ⬝ cellT h t) :=
  (appT_beta _ _).trans ((cellT_elim _ _ _ _ _ _).trans (appK1_beta _ _ _ _))

/-- **`app`** runs a `Form`'s code on the subject. -/
theorem app_form (h t c x : Term) : WSteps (appT ⬝ formT h t c ⬝ x) (c ⬝ x) :=
  (appT_beta _ _).trans ((formT_elim _ _ _ _ _ _ _).trans (appK2_beta _ _ _ _))

theorem app_err (x : Term) : WSteps (appT ⬝ errT ⬝ x) errT :=
  (appT_beta _ _).trans (errT_elim _ _ _ _)


end Nock2Ski
