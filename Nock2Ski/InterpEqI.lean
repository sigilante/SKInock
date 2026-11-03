import Nock2Ski.InterpEq

open Nock
open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

set_option linter.unusedSimpArgs false

/-!
# The structure of `nockO`, `nockP`, `nockI` and `app`, kernel-checked

The four equations that inline the whole interpreter (about 25,000 to
33,000 characters of SKI each): `nockO_eq`, `nockP_eq`, `nockI_eq`
(`= Ycomb ⬝ nockIG`), `app_eq`, and `nockIT_fix : nockI ↠ ω ω`, the
fixed point the simulation runs.
-/

namespace Nock2Ski

/-- `nockO`, compiled: its structure. -/
theorem nockO_eq : nockOT = toTerm (absNF [0, 1, 2, 3] (((((((((((((((.var 1) ⬝ₒ (((((.var 3) ⬝ₒ (nockOK0.toO ⬝ₒ .var 2)) ⬝ₒ nockOK1.toO) ⬝ₒ nockOK2.toO) ⬝ₒ ErrC.toO)) ⬝ₒ (.var 3)) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK5.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ (celT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 3)))) ⬝ₒ (incT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 3)))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK8.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK10.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK12.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK14.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK19.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK26.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ ((cel2T.toO ⬝ₒ (.var 3)) ⬝ₒ ((nockOK32.toO ⬝ₒ .var 0) ⬝ₒ .var 2))) ⬝ₒ (((op12T.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 2)) ⬝ₒ (.var 3))) ⬝ₒ ErrC.toO)) := by decide +kernel
/-- `nockP`, compiled: its structure. -/
theorem nockP_eq : nockPT = toTerm (absNF [0, 1, 2, 3] (((((.var 2) ⬝ₒ (((nockPK0.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 3)) ⬝ₒ ((((nockPK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 2) ⬝ₒ .var 3)) ⬝ₒ ((((nockPK2.toO ⬝ₒ .var 0) ⬝ₒ .var 1) ⬝ₒ .var 2) ⬝ₒ .var 3)) ⬝ₒ ErrC.toO)) := by decide +kernel
/-- `nockI = Y nockIG`. -/
theorem nockI_eq : nockIT = Ycomb ⬝ nockIG := by decide +kernel
/-- `nockI ↠ ω ω`. -/
theorem nockIT_fix : WSteps nockIT nockIFix := by rw [nockI_eq]; exact Ycomb_unroll _
/-- `app`, compiled: its structure. -/
theorem app_eq : appT = toTerm (absNF [0, 1] (((((.var 0) ⬝ₒ appK0.toO) ⬝ₒ ((appK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1)) ⬝ₒ (appK2.toO ⬝ₒ .var 1)) ⬝ₒ ErrC.toO)) := by decide +kernel
end Nock2Ski
