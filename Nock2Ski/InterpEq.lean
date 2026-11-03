import Nock2Ski.InterpDefs

open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

set_option linter.unusedSimpArgs false

/-!
# The structure of the helpers' terms, kernel-checked

`x_eq : xT = toTerm (absNF params body)` (or `Ycomb ⬝ xG` for `revb`,
`descend`, `editP`) for every helper of the interpreter: the file's term
(`termD`) has the lifted structure `InterpDefs.lean` writes out.  Each is
`decide +kernel`: the kernel compiles the equation through lean-ski's front
end and evaluates the structure, sharing the chain of dependencies
between the two sides.  The four terms that inline the whole interpreter
(`nockO`, `nockP`, `nockI`, `app`) are the next module.
-/

namespace Nock2Ski

/-- `decop11`, compiled: its structure. -/
theorem decop11_eq : decop11T = toTerm (absNF [0] (((.var 0) ⬝ₒ (opC 3).toO) ⬝ₒ decop11K3.toO)) := by decide +kernel
/-- `decop01`, compiled: its structure. -/
theorem decop01_eq : decop01T = toTerm (absNF [0] (((.var 0) ⬝ₒ (opC 13).toO) ⬝ₒ decop01K3.toO)) := by decide +kernel
/-- `decop10`, compiled: its structure. -/
theorem decop10_eq : decop10T = toTerm (absNF [0] (((.var 0) ⬝ₒ (opC 2).toO) ⬝ₒ decop10K3.toO)) := by decide +kernel
/-- `decop00`, compiled: its structure. -/
theorem decop00_eq : decop00T = toTerm (absNF [0] (((.var 0) ⬝ₒ (opC 13).toO) ⬝ₒ decop00K4.toO)) := by decide +kernel
/-- `revb = Y revbG`. -/
theorem revb_eq : revbT = Ycomb ⬝ revbG := by decide +kernel
/-- `revb ↠ ω ω`. -/
theorem revbT_fix : WSteps revbT revbFix := by rw [revb_eq]; exact Ycomb_unroll _
/-- `tlb`, compiled: its structure. -/
theorem tlb_eq : tlbT = toTerm (absNF [0] (((.var 0) ⬝ₒ NilC.toO) ⬝ₒ tlbK0.toO)) := by decide +kernel
/-- `path`, compiled: its structure. -/
theorem path_eq : pathT = toTerm (absNF [0] (tlbT.toO ⬝ₒ ((revbT.toO ⬝ₒ (.var 0)) ⬝ₒ NilC.toO))) := by decide +kernel
/-- `descend = Y descendG`. -/
theorem descend_eq : descendT = Ycomb ⬝ descendG := by decide +kernel
/-- `descend ↠ ω ω`. -/
theorem descendT_fix : WSteps descendT descendFix := by rw [descend_eq]; exact Ycomb_unroll _
/-- `slotB`, compiled: its structure. -/
theorem slotB_eq : slotBT = toTerm (absNF [0, 1] (((.var 0) ⬝ₒ ErrC.toO) ⬝ₒ (slotBK0.toO ⬝ₒ .var 1))) := by decide +kernel
/-- `editP = Y editPG`. -/
theorem editP_eq : editPT = Ycomb ⬝ editPG := by decide +kernel
/-- `editP ↠ ω ω`. -/
theorem editPT_fix : WSteps editPT editPFix := by rw [editP_eq]; exact Ycomb_unroll _
/-- `editB`, compiled: its structure. -/
theorem editB_eq : editBT = toTerm (absNF [0, 1, 2] (((.var 0) ⬝ₒ ErrC.toO) ⬝ₒ ((editBK0.toO ⬝ₒ .var 1) ⬝ₒ .var 2))) := by decide +kernel
/-- `autocons`, compiled: its structure. -/
theorem autocons_eq : autoconsT = toTerm (absNF [0, 1, 2, 3] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 1)) ⬝ₒ (.var 2))) ⬝ₒ (((autoconsK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 3))) := by decide +kernel
/-- `appI`, compiled: its structure. -/
theorem appI_eq : appIT = toTerm (absNF [0, 1, 2] (((((.var 1) ⬝ₒ appIK0.toO) ⬝ₒ (((appIK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 2)) ⬝ₒ (appIK2.toO ⬝ₒ .var 2)) ⬝ₒ ErrC.toO)) := by decide +kernel
/-- `cel2`, compiled: its structure. -/
theorem cel2_eq : cel2T = toTerm (absNF [0, 1] (((((.var 0) ⬝ₒ cel2K0.toO) ⬝ₒ (cel2K1.toO ⬝ₒ .var 1)) ⬝ₒ (cel2K2.toO ⬝ₒ .var 1)) ⬝ₒ ErrC.toO)) := by decide +kernel
/-- `op12`, compiled: its structure. -/
theorem op12_eq : op12T = toTerm (absNF [0, 1, 2] ErrC.toO) := by decide +kernel
/-- `decop1`, compiled: its structure. -/
theorem decop1_eq : decop1T = toTerm (absNF [0] (((.var 0) ⬝ₒ (opC 1).toO) ⬝ₒ decop1K0.toO)) := by decide +kernel
/-- `decop0`, compiled: its structure. -/
theorem decop0_eq : decop0T = toTerm (absNF [0] (((.var 0) ⬝ₒ (opC 13).toO) ⬝ₒ decop0K0.toO)) := by decide +kernel
/-- `decop`, compiled: its structure. -/
theorem decop_eq : decopT = toTerm (absNF [0] (((.var 0) ⬝ₒ (opC 0).toO) ⬝ₒ decopK0.toO)) := by decide +kernel
end Nock2Ski
