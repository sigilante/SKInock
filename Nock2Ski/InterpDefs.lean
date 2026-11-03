import Nock2Ski.Prims

open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

set_option linter.unusedSimpArgs false

/-!
# The interpreter's terms, as skijack lifts them

Milestone M3 of `PLAN.md`.  Each equation of `nock.ski`'s interpreter
fallback (`nockI`, `nockP`, `nockO`, `autocons`, `appI`, `cel2`, `decop…`,
`revb`, `tlb`, `path`, `descend`, `slotB`, `editP`, `editB`), the
compiler's default for opcode 12 (`op12`) and `app` is **defined as the
file's term** (`termD`, `Decls.lean`), and its structure is written out
beside it as `skijack` lifts the λs (`Ski/Compile.lean`'s `comp`): every
λ-chain is its own closed combinator over the binders it captures (in
scope order) and its own parameters, `xK0, xK1, …`, applied at its use
site to the captured binders.  `Interp.lean` tells the whole story; this
module has the definitions, β for every lifted combinator (`xK3_beta`,
…, `absN_beta_close` through `absNF` with the propositional
`close_app`/`close_var`/`close_toO`), and the selection lemmas of the
opcode tags (`opC_sel2 : O2 k0 … k13 ↠ k2`).  The structure of each
equation's term is the next two modules' kernel checks (`x_eq`).

The kernel-heavy theorems of M3 are spread over a chain of modules
(`InterpDefs → InterpEq → InterpEqI → InterpPins → InterpRuns → Interp`)
so that each `lean` process stays within about 4 GB.
-/

namespace Nock2Ski

/-- The `op` constructors `O0 … O12 Obad`: `λ k0 … k13. k_j`. -/
def opC (j : Nat) : Term := toTerm (absNF [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var j))

/-- β for `absNF`, lean-ski's linear-time bracket abstraction. -/
theorem absNF_beta_close (xs : List Nat) (M : OTerm) (γ : Nat → Term) (Ns : List Term)
    (h : Ns.length = xs.length) :
    WSteps (appT ((absNF xs M).close γ) Ns) (M.close (overrideC γ xs Ns)) := by
  rw [absNF_eq]; exact absN_beta_close xs M γ Ns h

/-- `OTerm.close` on an application and on a variable, as propositional
    rewrites: `simp` unfolding the structural recursion definitionally
    makes the kernel evaluate `Term.toO` of every constant in the term. -/
theorem close_app (σ : Nat → Term) (f x : OTerm) : (f ⬝ₒ x).close σ = f.close σ ⬝ x.close σ := by
  rw [OTerm.close]
theorem close_var (σ : Nat → Term) (i : Nat) : (OTerm.var i).close σ = σ i := by rw [OTerm.close]

-- decop11
/-- a λ of `decop11`: binders [3, 4], captured [] -/
def decop11K0 : Term := toTerm (absNF [3, 4] (opC 13).toO)
/-- a λ of `decop11`: binders [7, 8], captured [] -/
def decop11K1 : Term := toTerm (absNF [7, 8] (opC 13).toO)
/-- a λ of `decop11`: binders [5, 6], captured [] -/
def decop11K2 : Term := toTerm (absNF [5, 6] (((.var 5) ⬝ₒ (((.var 6) ⬝ₒ (opC 11).toO) ⬝ₒ decop11K1.toO)) ⬝ₒ (opC 13).toO))
/-- a λ of `decop11`: binders [1, 2], captured [] -/
def decop11K3 : Term := toTerm (absNF [1, 2] (((.var 1) ⬝ₒ (((.var 2) ⬝ₒ (opC 7).toO) ⬝ₒ decop11K0.toO)) ⬝ₒ (((.var 2) ⬝ₒ (opC 13).toO) ⬝ₒ decop11K2.toO)))
/-- `decop11`: the file's term. -/
def decop11T : Term := termD (nm! "decop11")

-- decop01
/-- a λ of `decop01`: binders [3, 4], captured [] -/
def decop01K0 : Term := toTerm (absNF [3, 4] (opC 13).toO)
/-- a λ of `decop01`: binders [7, 8], captured [] -/
def decop01K1 : Term := toTerm (absNF [7, 8] (opC 13).toO)
/-- a λ of `decop01`: binders [5, 6], captured [] -/
def decop01K2 : Term := toTerm (absNF [5, 6] (((.var 5) ⬝ₒ (((.var 6) ⬝ₒ (opC 9).toO) ⬝ₒ decop01K1.toO)) ⬝ₒ (opC 13).toO))
/-- a λ of `decop01`: binders [1, 2], captured [] -/
def decop01K3 : Term := toTerm (absNF [1, 2] (((.var 1) ⬝ₒ (((.var 2) ⬝ₒ (opC 5).toO) ⬝ₒ decop01K0.toO)) ⬝ₒ (((.var 2) ⬝ₒ (opC 13).toO) ⬝ₒ decop01K2.toO)))
/-- `decop01`: the file's term. -/
def decop01T : Term := termD (nm! "decop01")

-- decop10
/-- a λ of `decop10`: binders [3, 4], captured [] -/
def decop10K0 : Term := toTerm (absNF [3, 4] (opC 13).toO)
/-- a λ of `decop10`: binders [7, 8], captured [] -/
def decop10K1 : Term := toTerm (absNF [7, 8] (opC 13).toO)
/-- a λ of `decop10`: binders [5, 6], captured [] -/
def decop10K2 : Term := toTerm (absNF [5, 6] (((.var 5) ⬝ₒ (((.var 6) ⬝ₒ (opC 10).toO) ⬝ₒ decop10K1.toO)) ⬝ₒ (opC 13).toO))
/-- a λ of `decop10`: binders [1, 2], captured [] -/
def decop10K3 : Term := toTerm (absNF [1, 2] (((.var 1) ⬝ₒ (((.var 2) ⬝ₒ (opC 6).toO) ⬝ₒ decop10K0.toO)) ⬝ₒ (((.var 2) ⬝ₒ (opC 13).toO) ⬝ₒ decop10K2.toO)))
/-- `decop10`: the file's term. -/
def decop10T : Term := termD (nm! "decop10")

-- decop00
/-- a λ of `decop00`: binders [5, 6], captured [] -/
def decop00K0 : Term := toTerm (absNF [5, 6] (opC 13).toO)
/-- a λ of `decop00`: binders [3, 4], captured [] -/
def decop00K1 : Term := toTerm (absNF [3, 4] (((.var 3) ⬝ₒ (((.var 4) ⬝ₒ (opC 12).toO) ⬝ₒ decop00K0.toO)) ⬝ₒ (opC 13).toO))
/-- a λ of `decop00`: binders [9, 10], captured [] -/
def decop00K2 : Term := toTerm (absNF [9, 10] (opC 13).toO)
/-- a λ of `decop00`: binders [7, 8], captured [] -/
def decop00K3 : Term := toTerm (absNF [7, 8] (((.var 7) ⬝ₒ (((.var 8) ⬝ₒ (opC 8).toO) ⬝ₒ decop00K2.toO)) ⬝ₒ (opC 13).toO))
/-- a λ of `decop00`: binders [1, 2], captured [] -/
def decop00K4 : Term := toTerm (absNF [1, 2] (((.var 1) ⬝ₒ (((.var 2) ⬝ₒ (opC 4).toO) ⬝ₒ decop00K1.toO)) ⬝ₒ (((.var 2) ⬝ₒ (opC 13).toO) ⬝ₒ decop00K3.toO)))
/-- `decop00`: the file's term. -/
def decop00T : Term := termD (nm! "decop00")

-- revb
/-- a λ of `revb`: binders [3, 4], captured [0, 2] -/
def revbK0 : Term := toTerm (absNF [0, 2, 3, 4] (((.var 0) ⬝ₒ (.var 4)) ⬝ₒ ((ConsC.toO ⬝ₒ (.var 3)) ⬝ₒ (.var 2))))
/-- `revb`: the file's term. -/
def revbT : Term := termD (nm! "revb")
/-- `revb`'s generator: the abstraction over `revb` itself (`0`) and its parameters -/
def revbG : Term := toTerm (absNF [0, 1, 2] (((.var 1) ⬝ₒ (.var 2)) ⬝ₒ ((revbK0.toO ⬝ₒ .var 0) ⬝ₒ .var 2)))
/-- `ω ω` for `revb`, the fixed point `Y revbG` reaches. -/
def revbFix : Term := yfix revbG
theorem revb_unfold : WSteps revbFix (revbG ⬝ revbFix) := yfix_unroll _

-- tlb
/-- a λ of `tlb`: binders [1, 2], captured [] -/
def tlbK0 : Term := toTerm (absNF [1, 2] (.var 2))
/-- `tlb`: the file's term. -/
def tlbT : Term := termD (nm! "tlb")

-- path
/-- `path`: the file's term. -/
def pathT : Term := termD (nm! "path")

-- descend
/-- a λ of `descend`: binders [3, 4], captured [0, 2] -/
def descendK0 : Term := toTerm (absNF [0, 2, 3, 4] (((.var 3) ⬝ₒ (((.var 0) ⬝ₒ (.var 4)) ⬝ₒ (tlT.toO ⬝ₒ (.var 2)))) ⬝ₒ (((.var 0) ⬝ₒ (.var 4)) ⬝ₒ (hdT.toO ⬝ₒ (.var 2)))))
/-- `descend`: the file's term. -/
def descendT : Term := termD (nm! "descend")
/-- `descend`'s generator: the abstraction over `descend` itself (`0`) and its parameters -/
def descendG : Term := toTerm (absNF [0, 1, 2] (((.var 1) ⬝ₒ (.var 2)) ⬝ₒ ((descendK0.toO ⬝ₒ .var 0) ⬝ₒ .var 2)))
/-- `ω ω` for `descend`, the fixed point `Y descendG` reaches. -/
def descendFix : Term := yfix descendG
theorem descend_unfold : WSteps descendFix (descendG ⬝ descendFix) := yfix_unroll _

-- slotB
/-- a λ of `slotB`: binders [2, 3], captured [1] -/
def slotBK0 : Term := toTerm (absNF [1, 2, 3] ((descendT.toO ⬝ₒ (pathT.toO ⬝ₒ ((ConsC.toO ⬝ₒ (.var 2)) ⬝ₒ (.var 3)))) ⬝ₒ (.var 1)))
/-- `slotB`: the file's term. -/
def slotBT : Term := termD (nm! "slotB")

-- editP
/-- a λ of `editP`: binders [8], captured [6] -/
def editPK0 : Term := toTerm (absNF [6, 8] ((CellC.toO ⬝ₒ (.var 6)) ⬝ₒ (.var 8)))
/-- a λ of `editP`: binders [9], captured [7] -/
def editPK1 : Term := toTerm (absNF [7, 9] ((CellC.toO ⬝ₒ (.var 9)) ⬝ₒ (.var 7)))
/-- a λ of `editP`: binders [7], captured [0, 2, 4, 5, 6] -/
def editPK2 : Term := toTerm (absNF [0, 2, 4, 5, 6, 7] (((.var 4) ⬝ₒ ((forceT.toO ⬝ₒ ((((.var 0) ⬝ₒ (.var 5)) ⬝ₒ (.var 2)) ⬝ₒ (.var 7))) ⬝ₒ (editPK0.toO ⬝ₒ .var 6))) ⬝ₒ ((forceT.toO ⬝ₒ ((((.var 0) ⬝ₒ (.var 5)) ⬝ₒ (.var 2)) ⬝ₒ (.var 6))) ⬝ₒ (editPK1.toO ⬝ₒ .var 7))))
/-- a λ of `editP`: binders [6], captured [0, 2, 3, 4, 5] -/
def editPK3 : Term := toTerm (absNF [0, 2, 3, 4, 5, 6] ((forceT.toO ⬝ₒ (tlT.toO ⬝ₒ (.var 3))) ⬝ₒ (((((editPK2.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 4) ⬝ₒ .var 5) ⬝ₒ .var 6)))
/-- a λ of `editP`: binders [4, 5], captured [0, 2, 3] -/
def editPK4 : Term := toTerm (absNF [0, 2, 3, 4, 5] ((forceT.toO ⬝ₒ (hdT.toO ⬝ₒ (.var 3))) ⬝ₒ (((((editPK3.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 3) ⬝ₒ .var 4) ⬝ₒ .var 5)))
/-- `editP`: the file's term. -/
def editPT : Term := termD (nm! "editP")
/-- `editP`'s generator: the abstraction over `editP` itself (`0`) and its parameters -/
def editPG : Term := toTerm (absNF [0, 1, 2, 3] (((.var 1) ⬝ₒ (.var 2)) ⬝ₒ (((editPK4.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 3)))
/-- `ω ω` for `editP`, the fixed point `Y editPG` reaches. -/
def editPFix : Term := yfix editPG
theorem editP_unfold : WSteps editPFix (editPG ⬝ editPFix) := yfix_unroll _

-- editB
/-- a λ of `editB`: binders [3, 4], captured [1, 2] -/
def editBK0 : Term := toTerm (absNF [1, 2, 3, 4] (((editPT.toO ⬝ₒ (pathT.toO ⬝ₒ ((ConsC.toO ⬝ₒ (.var 3)) ⬝ₒ (.var 4)))) ⬝ₒ (.var 1)) ⬝ₒ (.var 2)))
/-- `editB`: the file's term. -/
def editBT : Term := termD (nm! "editB")

-- autocons
/-- a λ of `autocons`: binders [5], captured [4] -/
def autoconsK0 : Term := toTerm (absNF [4, 5] ((CellC.toO ⬝ₒ (.var 4)) ⬝ₒ (.var 5)))
/-- a λ of `autocons`: binders [4], captured [0, 1, 3] -/
def autoconsK1 : Term := toTerm (absNF [0, 1, 3, 4] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 1)) ⬝ₒ (.var 3))) ⬝ₒ (autoconsK0.toO ⬝ₒ .var 4)))
/-- `autocons`: the file's term. -/
def autoconsT : Term := termD (nm! "autocons")

-- appI
/-- a λ of `appI`: binders [3], captured [] -/
def appIK0 : Term := toTerm (absNF [3] ErrC.toO)
/-- a λ of `appI`: binders [4, 5], captured [0, 1, 2] -/
def appIK1 : Term := toTerm (absNF [0, 1, 2, 4, 5] (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 1)))
/-- a λ of `appI`: binders [6, 7, 8], captured [2] -/
def appIK2 : Term := toTerm (absNF [2, 6, 7, 8] ((.var 8) ⬝ₒ (.var 2)))
/-- `appI`: the file's term. -/
def appIT : Term := termD (nm! "appI")

-- cel2
/-- a λ of `cel2`: binders [2], captured [] -/
def cel2K0 : Term := toTerm (absNF [2] ErrC.toO)
/-- a λ of `cel2`: binders [3, 4], captured [1] -/
def cel2K1 : Term := toTerm (absNF [1, 3, 4] (((.var 1) ⬝ₒ (.var 3)) ⬝ₒ (.var 4)))
/-- a λ of `cel2`: binders [5, 6, 7], captured [1] -/
def cel2K2 : Term := toTerm (absNF [1, 5, 6, 7] (((.var 1) ⬝ₒ (.var 5)) ⬝ₒ (.var 6)))
/-- `cel2`: the file's term. -/
def cel2T : Term := termD (nm! "cel2")

-- op12
/-- `op12`: the file's term. -/
def op12T : Term := termD (nm! "op12")

-- decop1
/-- a λ of `decop1`: binders [1, 2], captured [] -/
def decop1K0 : Term := toTerm (absNF [1, 2] (((.var 1) ⬝ₒ (decop11T.toO ⬝ₒ (.var 2))) ⬝ₒ (decop01T.toO ⬝ₒ (.var 2))))
/-- `decop1`: the file's term. -/
def decop1T : Term := termD (nm! "decop1")

-- decop0
/-- a λ of `decop0`: binders [1, 2], captured [] -/
def decop0K0 : Term := toTerm (absNF [1, 2] (((.var 1) ⬝ₒ (decop10T.toO ⬝ₒ (.var 2))) ⬝ₒ (decop00T.toO ⬝ₒ (.var 2))))
/-- `decop0`: the file's term. -/
def decop0T : Term := termD (nm! "decop0")

-- nockO
/-- a λ of `nockO`: binders [4], captured [2] -/
def nockOK0 : Term := toTerm (absNF [2, 4] ((slotBT.toO ⬝ₒ (.var 4)) ⬝ₒ (.var 2)))
/-- a λ of `nockO`: binders [5, 6], captured [] -/
def nockOK1 : Term := toTerm (absNF [5, 6] ErrC.toO)
/-- a λ of `nockO`: binders [7, 8, 9], captured [] -/
def nockOK2 : Term := toTerm (absNF [7, 8, 9] ErrC.toO)
/-- a λ of `nockO`: binders [13], captured [0, 12] -/
def nockOK3 : Term := toTerm (absNF [0, 12, 13] (((appIT.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 13)) ⬝ₒ (.var 12)))
/-- a λ of `nockO`: binders [12], captured [0, 2, 11] -/
def nockOK4 : Term := toTerm (absNF [0, 2, 11, 12] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 11))) ⬝ₒ ((nockOK3.toO ⬝ₒ .var 0) ⬝ₒ .var 12)))
/-- a λ of `nockO`: binders [10, 11], captured [0, 2] -/
def nockOK5 : Term := toTerm (absNF [0, 2, 10, 11] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 10))) ⬝ₒ (((nockOK4.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 11)))
/-- a λ of `nockO`: binders [17], captured [16] -/
def nockOK6 : Term := toTerm (absNF [16, 17] ((eqT.toO ⬝ₒ (.var 16)) ⬝ₒ (.var 17)))
/-- a λ of `nockO`: binders [16], captured [0, 2, 15] -/
def nockOK7 : Term := toTerm (absNF [0, 2, 15, 16] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 15))) ⬝ₒ (nockOK6.toO ⬝ₒ .var 16)))
/-- a λ of `nockO`: binders [14, 15], captured [0, 2] -/
def nockOK8 : Term := toTerm (absNF [0, 2, 14, 15] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 14))) ⬝ₒ (((nockOK7.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 15)))
/-- a λ of `nockO`: binders [20, 21], captured [0, 2, 18] -/
def nockOK9 : Term := toTerm (absNF [0, 2, 18, 20, 21] (((ifnT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 18))) ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 20))) ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 21))))
/-- a λ of `nockO`: binders [18, 19], captured [0, 2] -/
def nockOK10 : Term := toTerm (absNF [0, 2, 18, 19] ((cel2T.toO ⬝ₒ (.var 19)) ⬝ₒ (((nockOK9.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 18)))
/-- a λ of `nockO`: binders [24], captured [0, 23] -/
def nockOK11 : Term := toTerm (absNF [0, 23, 24] (((.var 0) ⬝ₒ (.var 24)) ⬝ₒ (.var 23)))
/-- a λ of `nockO`: binders [22, 23], captured [0, 2] -/
def nockOK12 : Term := toTerm (absNF [0, 2, 22, 23] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 22))) ⬝ₒ ((nockOK11.toO ⬝ₒ .var 0) ⬝ₒ .var 23)))
/-- a λ of `nockO`: binders [27], captured [0, 2, 26] -/
def nockOK13 : Term := toTerm (absNF [0, 2, 26, 27] (((.var 0) ⬝ₒ ((CellC.toO ⬝ₒ (.var 27)) ⬝ₒ (.var 2))) ⬝ₒ (.var 26)))
/-- a λ of `nockO`: binders [25, 26], captured [0, 2] -/
def nockOK14 : Term := toTerm (absNF [0, 2, 25, 26] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 25))) ⬝ₒ (((nockOK13.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 26)))
/-- a λ of `nockO`: binders [31], captured [0, 30] -/
def nockOK15 : Term := toTerm (absNF [0, 30, 31] (((appIT.toO ⬝ₒ (.var 0)) ⬝ₒ ((slotBT.toO ⬝ₒ (.var 31)) ⬝ₒ (.var 30))) ⬝ₒ (.var 30)))
/-- a λ of `nockO`: binders [32, 33], captured [] -/
def nockOK16 : Term := toTerm (absNF [32, 33] ErrC.toO)
/-- a λ of `nockO`: binders [34, 35, 36], captured [] -/
def nockOK17 : Term := toTerm (absNF [34, 35, 36] ErrC.toO)
/-- a λ of `nockO`: binders [30], captured [0, 28] -/
def nockOK18 : Term := toTerm (absNF [0, 28, 30] (((((.var 28) ⬝ₒ ((nockOK15.toO ⬝ₒ .var 0) ⬝ₒ .var 30)) ⬝ₒ nockOK16.toO) ⬝ₒ nockOK17.toO) ⬝ₒ ErrC.toO))
/-- a λ of `nockO`: binders [28, 29], captured [0, 2] -/
def nockOK19 : Term := toTerm (absNF [0, 2, 28, 29] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 29))) ⬝ₒ ((nockOK18.toO ⬝ₒ .var 0) ⬝ₒ .var 28)))
/-- a λ of `nockO`: binders [43], captured [41, 42] -/
def nockOK20 : Term := toTerm (absNF [41, 42, 43] (((editBT.toO ⬝ₒ (.var 43)) ⬝ₒ (.var 42)) ⬝ₒ (.var 41)))
/-- a λ of `nockO`: binders [44, 45], captured [] -/
def nockOK21 : Term := toTerm (absNF [44, 45] ErrC.toO)
/-- a λ of `nockO`: binders [46, 47, 48], captured [] -/
def nockOK22 : Term := toTerm (absNF [46, 47, 48] ErrC.toO)
/-- a λ of `nockO`: binders [42], captured [39, 41] -/
def nockOK23 : Term := toTerm (absNF [39, 41, 42] (((((.var 39) ⬝ₒ ((nockOK20.toO ⬝ₒ .var 41) ⬝ₒ .var 42)) ⬝ₒ nockOK21.toO) ⬝ₒ nockOK22.toO) ⬝ₒ ErrC.toO))
/-- a λ of `nockO`: binders [41], captured [0, 2, 39, 40] -/
def nockOK24 : Term := toTerm (absNF [0, 2, 39, 40, 41] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 40))) ⬝ₒ ((nockOK23.toO ⬝ₒ .var 39) ⬝ₒ .var 41)))
/-- a λ of `nockO`: binders [39, 40], captured [0, 2, 38] -/
def nockOK25 : Term := toTerm (absNF [0, 2, 38, 39, 40] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 38))) ⬝ₒ ((((nockOK24.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 39) ⬝ₒ .var 40)))
/-- a λ of `nockO`: binders [37, 38], captured [0, 2] -/
def nockOK26 : Term := toTerm (absNF [0, 2, 37, 38] ((cel2T.toO ⬝ₒ (.var 37)) ⬝ₒ (((nockOK25.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 38)))
/-- a λ of `nockO`: binders [51], captured [0, 2, 50] -/
def nockOK27 : Term := toTerm (absNF [0, 2, 50, 51] (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 50)))
/-- a λ of `nockO`: binders [54], captured [0, 2, 50] -/
def nockOK28 : Term := toTerm (absNF [0, 2, 50, 54] (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 50)))
/-- a λ of `nockO`: binders [52, 53], captured [0, 2, 50] -/
def nockOK29 : Term := toTerm (absNF [0, 2, 50, 52, 53] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 53))) ⬝ₒ (((nockOK28.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)))
/-- a λ of `nockO`: binders [58], captured [0, 2, 50] -/
def nockOK30 : Term := toTerm (absNF [0, 2, 50, 58] (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 50)))
/-- a λ of `nockO`: binders [55, 56, 57], captured [0, 2, 50] -/
def nockOK31 : Term := toTerm (absNF [0, 2, 50, 55, 56, 57] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 56))) ⬝ₒ (((nockOK30.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)))
/-- a λ of `nockO`: binders [49, 50], captured [0, 2] -/
def nockOK32 : Term := toTerm (absNF [0, 2, 49, 50] (((((.var 49) ⬝ₒ (((nockOK27.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)) ⬝ₒ (((nockOK29.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)) ⬝ₒ (((nockOK31.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)) ⬝ₒ ErrC.toO))
/-- `nockO`: the file's term. -/
def nockOT : Term := termD (nm! "nockO")

-- decop
/-- a λ of `decop`: binders [1, 2], captured [] -/
def decopK0 : Term := toTerm (absNF [1, 2] (((.var 1) ⬝ₒ (decop1T.toO ⬝ₒ (.var 2))) ⬝ₒ (decop0T.toO ⬝ₒ (.var 2))))
/-- `decop`: the file's term. -/
def decopT : Term := termD (nm! "decop")

-- nockP
/-- a λ of `nockP`: binders [4], captured [0, 1, 3] -/
def nockPK0 : Term := toTerm (absNF [0, 1, 3, 4] ((((nockOT.toO ⬝ₒ (.var 0)) ⬝ₒ (decopT.toO ⬝ₒ (.var 4))) ⬝ₒ (.var 1)) ⬝ₒ (.var 3)))
/-- a λ of `nockP`: binders [5, 6], captured [0, 1, 2, 3] -/
def nockPK1 : Term := toTerm (absNF [0, 1, 2, 3, 5, 6] ((((autoconsT.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 1)) ⬝ₒ (.var 2)) ⬝ₒ (.var 3)))
/-- a λ of `nockP`: binders [7, 8, 9], captured [0, 1, 2, 3] -/
def nockPK2 : Term := toTerm (absNF [0, 1, 2, 3, 7, 8, 9] ((((autoconsT.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 1)) ⬝ₒ (.var 2)) ⬝ₒ (.var 3)))
/-- `nockP`: the file's term. -/
def nockPT : Term := termD (nm! "nockP")

-- nockI
/-- a λ of `nockI`: binders [3], captured [] -/
def nockIK0 : Term := toTerm (absNF [3] ErrC.toO)
/-- a λ of `nockI`: binders [4, 5], captured [0, 1] -/
def nockIK1 : Term := toTerm (absNF [0, 1, 4, 5] ((((nockPT.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 1)) ⬝ₒ (.var 4)) ⬝ₒ (.var 5)))
/-- a λ of `nockI`: binders [6, 7, 8], captured [1] -/
def nockIK2 : Term := toTerm (absNF [1, 6, 7, 8] ((.var 8) ⬝ₒ (.var 1)))
/-- `nockI`: the file's term. -/
def nockIT : Term := termD (nm! "nockI")
/-- `nockI`'s generator: the abstraction over `nockI` itself (`0`) and its parameters -/
def nockIG : Term := toTerm (absNF [0, 1, 2] (((((.var 2) ⬝ₒ nockIK0.toO) ⬝ₒ ((nockIK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1)) ⬝ₒ (nockIK2.toO ⬝ₒ .var 1)) ⬝ₒ ErrC.toO))
/-- `ω ω` for `nockI`, the fixed point `Y nockIG` reaches. -/
def nockIFix : Term := yfix nockIG
theorem nockI_unfold : WSteps nockIFix (nockIG ⬝ nockIFix) := yfix_unroll _

-- app
/-- a λ of `app`: binders [2], captured [] -/
def appK0 : Term := toTerm (absNF [2] ErrC.toO)
/-- a λ of `app`: binders [3, 4], captured [0, 1] -/
def appK1 : Term := toTerm (absNF [0, 1, 3, 4] ((nockIT.toO ⬝ₒ (.var 1)) ⬝ₒ (.var 0)))
/-- a λ of `app`: binders [5, 6, 7], captured [1] -/
def appK2 : Term := toTerm (absNF [1, 5, 6, 7] ((.var 7) ⬝ₒ (.var 1)))
/-- `app`: the file's term. -/
def appT : Term := termD (nm! "app")


theorem decop11K0_beta (x3 x4 : Term) :
    WSteps (decop11K0 ⬝ x3 ⬝ x4) (opC 13) := by
  have h := absNF_beta_close [3, 4] (opC 13).toO (fun _ => K) [x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop11K1_beta (x7 x8 : Term) :
    WSteps (decop11K1 ⬝ x7 ⬝ x8) (opC 13) := by
  have h := absNF_beta_close [7, 8] (opC 13).toO (fun _ => K) [x7, x8] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop11K2_beta (x5 x6 : Term) :
    WSteps (decop11K2 ⬝ x5 ⬝ x6) ((x5 ⬝ ((x6 ⬝ (opC 11)) ⬝ decop11K1)) ⬝ (opC 13)) := by
  have h := absNF_beta_close [5, 6] (((.var 5) ⬝ₒ (((.var 6) ⬝ₒ (opC 11).toO) ⬝ₒ decop11K1.toO)) ⬝ₒ (opC 13).toO) (fun _ => K) [x5, x6] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop11K3_beta (x1 x2 : Term) :
    WSteps (decop11K3 ⬝ x1 ⬝ x2) ((x1 ⬝ ((x2 ⬝ (opC 7)) ⬝ decop11K0)) ⬝ ((x2 ⬝ (opC 13)) ⬝ decop11K2)) := by
  have h := absNF_beta_close [1, 2] (((.var 1) ⬝ₒ (((.var 2) ⬝ₒ (opC 7).toO) ⬝ₒ decop11K0.toO)) ⬝ₒ (((.var 2) ⬝ₒ (opC 13).toO) ⬝ₒ decop11K2.toO)) (fun _ => K) [x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop01K0_beta (x3 x4 : Term) :
    WSteps (decop01K0 ⬝ x3 ⬝ x4) (opC 13) := by
  have h := absNF_beta_close [3, 4] (opC 13).toO (fun _ => K) [x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop01K1_beta (x7 x8 : Term) :
    WSteps (decop01K1 ⬝ x7 ⬝ x8) (opC 13) := by
  have h := absNF_beta_close [7, 8] (opC 13).toO (fun _ => K) [x7, x8] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop01K2_beta (x5 x6 : Term) :
    WSteps (decop01K2 ⬝ x5 ⬝ x6) ((x5 ⬝ ((x6 ⬝ (opC 9)) ⬝ decop01K1)) ⬝ (opC 13)) := by
  have h := absNF_beta_close [5, 6] (((.var 5) ⬝ₒ (((.var 6) ⬝ₒ (opC 9).toO) ⬝ₒ decop01K1.toO)) ⬝ₒ (opC 13).toO) (fun _ => K) [x5, x6] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop01K3_beta (x1 x2 : Term) :
    WSteps (decop01K3 ⬝ x1 ⬝ x2) ((x1 ⬝ ((x2 ⬝ (opC 5)) ⬝ decop01K0)) ⬝ ((x2 ⬝ (opC 13)) ⬝ decop01K2)) := by
  have h := absNF_beta_close [1, 2] (((.var 1) ⬝ₒ (((.var 2) ⬝ₒ (opC 5).toO) ⬝ₒ decop01K0.toO)) ⬝ₒ (((.var 2) ⬝ₒ (opC 13).toO) ⬝ₒ decop01K2.toO)) (fun _ => K) [x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop10K0_beta (x3 x4 : Term) :
    WSteps (decop10K0 ⬝ x3 ⬝ x4) (opC 13) := by
  have h := absNF_beta_close [3, 4] (opC 13).toO (fun _ => K) [x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop10K1_beta (x7 x8 : Term) :
    WSteps (decop10K1 ⬝ x7 ⬝ x8) (opC 13) := by
  have h := absNF_beta_close [7, 8] (opC 13).toO (fun _ => K) [x7, x8] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop10K2_beta (x5 x6 : Term) :
    WSteps (decop10K2 ⬝ x5 ⬝ x6) ((x5 ⬝ ((x6 ⬝ (opC 10)) ⬝ decop10K1)) ⬝ (opC 13)) := by
  have h := absNF_beta_close [5, 6] (((.var 5) ⬝ₒ (((.var 6) ⬝ₒ (opC 10).toO) ⬝ₒ decop10K1.toO)) ⬝ₒ (opC 13).toO) (fun _ => K) [x5, x6] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop10K3_beta (x1 x2 : Term) :
    WSteps (decop10K3 ⬝ x1 ⬝ x2) ((x1 ⬝ ((x2 ⬝ (opC 6)) ⬝ decop10K0)) ⬝ ((x2 ⬝ (opC 13)) ⬝ decop10K2)) := by
  have h := absNF_beta_close [1, 2] (((.var 1) ⬝ₒ (((.var 2) ⬝ₒ (opC 6).toO) ⬝ₒ decop10K0.toO)) ⬝ₒ (((.var 2) ⬝ₒ (opC 13).toO) ⬝ₒ decop10K2.toO)) (fun _ => K) [x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop00K0_beta (x5 x6 : Term) :
    WSteps (decop00K0 ⬝ x5 ⬝ x6) (opC 13) := by
  have h := absNF_beta_close [5, 6] (opC 13).toO (fun _ => K) [x5, x6] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop00K1_beta (x3 x4 : Term) :
    WSteps (decop00K1 ⬝ x3 ⬝ x4) ((x3 ⬝ ((x4 ⬝ (opC 12)) ⬝ decop00K0)) ⬝ (opC 13)) := by
  have h := absNF_beta_close [3, 4] (((.var 3) ⬝ₒ (((.var 4) ⬝ₒ (opC 12).toO) ⬝ₒ decop00K0.toO)) ⬝ₒ (opC 13).toO) (fun _ => K) [x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop00K2_beta (x9 x10 : Term) :
    WSteps (decop00K2 ⬝ x9 ⬝ x10) (opC 13) := by
  have h := absNF_beta_close [9, 10] (opC 13).toO (fun _ => K) [x9, x10] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop00K3_beta (x7 x8 : Term) :
    WSteps (decop00K3 ⬝ x7 ⬝ x8) ((x7 ⬝ ((x8 ⬝ (opC 8)) ⬝ decop00K2)) ⬝ (opC 13)) := by
  have h := absNF_beta_close [7, 8] (((.var 7) ⬝ₒ (((.var 8) ⬝ₒ (opC 8).toO) ⬝ₒ decop00K2.toO)) ⬝ₒ (opC 13).toO) (fun _ => K) [x7, x8] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop00K4_beta (x1 x2 : Term) :
    WSteps (decop00K4 ⬝ x1 ⬝ x2) ((x1 ⬝ ((x2 ⬝ (opC 4)) ⬝ decop00K1)) ⬝ ((x2 ⬝ (opC 13)) ⬝ decop00K3)) := by
  have h := absNF_beta_close [1, 2] (((.var 1) ⬝ₒ (((.var 2) ⬝ₒ (opC 4).toO) ⬝ₒ decop00K1.toO)) ⬝ₒ (((.var 2) ⬝ₒ (opC 13).toO) ⬝ₒ decop00K3.toO)) (fun _ => K) [x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem revbK0_beta (x0 x2 x3 x4 : Term) :
    WSteps (revbK0 ⬝ x0 ⬝ x2 ⬝ x3 ⬝ x4) ((x0 ⬝ x4) ⬝ ((ConsC ⬝ x3) ⬝ x2)) := by
  have h := absNF_beta_close [0, 2, 3, 4] (((.var 0) ⬝ₒ (.var 4)) ⬝ₒ ((ConsC.toO ⬝ₒ (.var 3)) ⬝ₒ (.var 2))) (fun _ => K) [x0, x2, x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem revbG_beta (x0 x1 x2 : Term) :
    WSteps (revbG ⬝ x0 ⬝ x1 ⬝ x2) ((x1 ⬝ x2) ⬝ ((revbK0 ⬝ x0) ⬝ x2)) := by
  have h := absNF_beta_close [0, 1, 2] (((.var 1) ⬝ₒ (.var 2)) ⬝ₒ ((revbK0.toO ⬝ₒ .var 0) ⬝ₒ .var 2)) (fun _ => K) [x0, x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem tlbK0_beta (x1 x2 : Term) :
    WSteps (tlbK0 ⬝ x1 ⬝ x2) x2 := by
  have h := absNF_beta_close [1, 2] (.var 2) (fun _ => K) [x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem descendK0_beta (x0 x2 x3 x4 : Term) :
    WSteps (descendK0 ⬝ x0 ⬝ x2 ⬝ x3 ⬝ x4) ((x3 ⬝ ((x0 ⬝ x4) ⬝ (tlT ⬝ x2))) ⬝ ((x0 ⬝ x4) ⬝ (hdT ⬝ x2))) := by
  have h := absNF_beta_close [0, 2, 3, 4] (((.var 3) ⬝ₒ (((.var 0) ⬝ₒ (.var 4)) ⬝ₒ (tlT.toO ⬝ₒ (.var 2)))) ⬝ₒ (((.var 0) ⬝ₒ (.var 4)) ⬝ₒ (hdT.toO ⬝ₒ (.var 2)))) (fun _ => K) [x0, x2, x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem descendG_beta (x0 x1 x2 : Term) :
    WSteps (descendG ⬝ x0 ⬝ x1 ⬝ x2) ((x1 ⬝ x2) ⬝ ((descendK0 ⬝ x0) ⬝ x2)) := by
  have h := absNF_beta_close [0, 1, 2] (((.var 1) ⬝ₒ (.var 2)) ⬝ₒ ((descendK0.toO ⬝ₒ .var 0) ⬝ₒ .var 2)) (fun _ => K) [x0, x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem slotBK0_beta (x1 x2 x3 : Term) :
    WSteps (slotBK0 ⬝ x1 ⬝ x2 ⬝ x3) ((descendT ⬝ (pathT ⬝ ((ConsC ⬝ x2) ⬝ x3))) ⬝ x1) := by
  have h := absNF_beta_close [1, 2, 3] ((descendT.toO ⬝ₒ (pathT.toO ⬝ₒ ((ConsC.toO ⬝ₒ (.var 2)) ⬝ₒ (.var 3)))) ⬝ₒ (.var 1)) (fun _ => K) [x1, x2, x3] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem editPK0_beta (x6 x8 : Term) :
    WSteps (editPK0 ⬝ x6 ⬝ x8) ((CellC ⬝ x6) ⬝ x8) := by
  have h := absNF_beta_close [6, 8] ((CellC.toO ⬝ₒ (.var 6)) ⬝ₒ (.var 8)) (fun _ => K) [x6, x8] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem editPK1_beta (x7 x9 : Term) :
    WSteps (editPK1 ⬝ x7 ⬝ x9) ((CellC ⬝ x9) ⬝ x7) := by
  have h := absNF_beta_close [7, 9] ((CellC.toO ⬝ₒ (.var 9)) ⬝ₒ (.var 7)) (fun _ => K) [x7, x9] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem editPK2_beta (x0 x2 x4 x5 x6 x7 : Term) :
    WSteps (editPK2 ⬝ x0 ⬝ x2 ⬝ x4 ⬝ x5 ⬝ x6 ⬝ x7) ((x4 ⬝ ((forceT ⬝ (((x0 ⬝ x5) ⬝ x2) ⬝ x7)) ⬝ (editPK0 ⬝ x6))) ⬝ ((forceT ⬝ (((x0 ⬝ x5) ⬝ x2) ⬝ x6)) ⬝ (editPK1 ⬝ x7))) := by
  have h := absNF_beta_close [0, 2, 4, 5, 6, 7] (((.var 4) ⬝ₒ ((forceT.toO ⬝ₒ ((((.var 0) ⬝ₒ (.var 5)) ⬝ₒ (.var 2)) ⬝ₒ (.var 7))) ⬝ₒ (editPK0.toO ⬝ₒ .var 6))) ⬝ₒ ((forceT.toO ⬝ₒ ((((.var 0) ⬝ₒ (.var 5)) ⬝ₒ (.var 2)) ⬝ₒ (.var 6))) ⬝ₒ (editPK1.toO ⬝ₒ .var 7))) (fun _ => K) [x0, x2, x4, x5, x6, x7] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem editPK3_beta (x0 x2 x3 x4 x5 x6 : Term) :
    WSteps (editPK3 ⬝ x0 ⬝ x2 ⬝ x3 ⬝ x4 ⬝ x5 ⬝ x6) ((forceT ⬝ (tlT ⬝ x3)) ⬝ (((((editPK2 ⬝ x0) ⬝ x2) ⬝ x4) ⬝ x5) ⬝ x6)) := by
  have h := absNF_beta_close [0, 2, 3, 4, 5, 6] ((forceT.toO ⬝ₒ (tlT.toO ⬝ₒ (.var 3))) ⬝ₒ (((((editPK2.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 4) ⬝ₒ .var 5) ⬝ₒ .var 6)) (fun _ => K) [x0, x2, x3, x4, x5, x6] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem editPK4_beta (x0 x2 x3 x4 x5 : Term) :
    WSteps (editPK4 ⬝ x0 ⬝ x2 ⬝ x3 ⬝ x4 ⬝ x5) ((forceT ⬝ (hdT ⬝ x3)) ⬝ (((((editPK3 ⬝ x0) ⬝ x2) ⬝ x3) ⬝ x4) ⬝ x5)) := by
  have h := absNF_beta_close [0, 2, 3, 4, 5] ((forceT.toO ⬝ₒ (hdT.toO ⬝ₒ (.var 3))) ⬝ₒ (((((editPK3.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 3) ⬝ₒ .var 4) ⬝ₒ .var 5)) (fun _ => K) [x0, x2, x3, x4, x5] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem editPG_beta (x0 x1 x2 x3 : Term) :
    WSteps (editPG ⬝ x0 ⬝ x1 ⬝ x2 ⬝ x3) ((x1 ⬝ x2) ⬝ (((editPK4 ⬝ x0) ⬝ x2) ⬝ x3)) := by
  have h := absNF_beta_close [0, 1, 2, 3] (((.var 1) ⬝ₒ (.var 2)) ⬝ₒ (((editPK4.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 3)) (fun _ => K) [x0, x1, x2, x3] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem editBK0_beta (x1 x2 x3 x4 : Term) :
    WSteps (editBK0 ⬝ x1 ⬝ x2 ⬝ x3 ⬝ x4) (((editPT ⬝ (pathT ⬝ ((ConsC ⬝ x3) ⬝ x4))) ⬝ x1) ⬝ x2) := by
  have h := absNF_beta_close [1, 2, 3, 4] (((editPT.toO ⬝ₒ (pathT.toO ⬝ₒ ((ConsC.toO ⬝ₒ (.var 3)) ⬝ₒ (.var 4)))) ⬝ₒ (.var 1)) ⬝ₒ (.var 2)) (fun _ => K) [x1, x2, x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem autoconsK0_beta (x4 x5 : Term) :
    WSteps (autoconsK0 ⬝ x4 ⬝ x5) ((CellC ⬝ x4) ⬝ x5) := by
  have h := absNF_beta_close [4, 5] ((CellC.toO ⬝ₒ (.var 4)) ⬝ₒ (.var 5)) (fun _ => K) [x4, x5] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem autoconsK1_beta (x0 x1 x3 x4 : Term) :
    WSteps (autoconsK1 ⬝ x0 ⬝ x1 ⬝ x3 ⬝ x4) ((forceT ⬝ ((x0 ⬝ x1) ⬝ x3)) ⬝ (autoconsK0 ⬝ x4)) := by
  have h := absNF_beta_close [0, 1, 3, 4] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 1)) ⬝ₒ (.var 3))) ⬝ₒ (autoconsK0.toO ⬝ₒ .var 4)) (fun _ => K) [x0, x1, x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appIK0_beta (x3 : Term) :
    WSteps (appIK0 ⬝ x3) ErrC := by
  have h := absNF_beta_close [3] ErrC.toO (fun _ => K) [x3] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appIK1_beta (x0 x1 x2 x4 x5 : Term) :
    WSteps (appIK1 ⬝ x0 ⬝ x1 ⬝ x2 ⬝ x4 ⬝ x5) ((x0 ⬝ x2) ⬝ x1) := by
  have h := absNF_beta_close [0, 1, 2, 4, 5] (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 1)) (fun _ => K) [x0, x1, x2, x4, x5] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appIK2_beta (x2 x6 x7 x8 : Term) :
    WSteps (appIK2 ⬝ x2 ⬝ x6 ⬝ x7 ⬝ x8) (x8 ⬝ x2) := by
  have h := absNF_beta_close [2, 6, 7, 8] ((.var 8) ⬝ₒ (.var 2)) (fun _ => K) [x2, x6, x7, x8] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem cel2K0_beta (x2 : Term) :
    WSteps (cel2K0 ⬝ x2) ErrC := by
  have h := absNF_beta_close [2] ErrC.toO (fun _ => K) [x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem cel2K1_beta (x1 x3 x4 : Term) :
    WSteps (cel2K1 ⬝ x1 ⬝ x3 ⬝ x4) ((x1 ⬝ x3) ⬝ x4) := by
  have h := absNF_beta_close [1, 3, 4] (((.var 1) ⬝ₒ (.var 3)) ⬝ₒ (.var 4)) (fun _ => K) [x1, x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem cel2K2_beta (x1 x5 x6 x7 : Term) :
    WSteps (cel2K2 ⬝ x1 ⬝ x5 ⬝ x6 ⬝ x7) ((x1 ⬝ x5) ⬝ x6) := by
  have h := absNF_beta_close [1, 5, 6, 7] (((.var 1) ⬝ₒ (.var 5)) ⬝ₒ (.var 6)) (fun _ => K) [x1, x5, x6, x7] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop1K0_beta (x1 x2 : Term) :
    WSteps (decop1K0 ⬝ x1 ⬝ x2) ((x1 ⬝ (decop11T ⬝ x2)) ⬝ (decop01T ⬝ x2)) := by
  have h := absNF_beta_close [1, 2] (((.var 1) ⬝ₒ (decop11T.toO ⬝ₒ (.var 2))) ⬝ₒ (decop01T.toO ⬝ₒ (.var 2))) (fun _ => K) [x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decop0K0_beta (x1 x2 : Term) :
    WSteps (decop0K0 ⬝ x1 ⬝ x2) ((x1 ⬝ (decop10T ⬝ x2)) ⬝ (decop00T ⬝ x2)) := by
  have h := absNF_beta_close [1, 2] (((.var 1) ⬝ₒ (decop10T.toO ⬝ₒ (.var 2))) ⬝ₒ (decop00T.toO ⬝ₒ (.var 2))) (fun _ => K) [x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK0_beta (x2 x4 : Term) :
    WSteps (nockOK0 ⬝ x2 ⬝ x4) ((slotBT ⬝ x4) ⬝ x2) := by
  have h := absNF_beta_close [2, 4] ((slotBT.toO ⬝ₒ (.var 4)) ⬝ₒ (.var 2)) (fun _ => K) [x2, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK1_beta (x5 x6 : Term) :
    WSteps (nockOK1 ⬝ x5 ⬝ x6) ErrC := by
  have h := absNF_beta_close [5, 6] ErrC.toO (fun _ => K) [x5, x6] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK2_beta (x7 x8 x9 : Term) :
    WSteps (nockOK2 ⬝ x7 ⬝ x8 ⬝ x9) ErrC := by
  have h := absNF_beta_close [7, 8, 9] ErrC.toO (fun _ => K) [x7, x8, x9] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK3_beta (x0 x12 x13 : Term) :
    WSteps (nockOK3 ⬝ x0 ⬝ x12 ⬝ x13) (((appIT ⬝ x0) ⬝ x13) ⬝ x12) := by
  have h := absNF_beta_close [0, 12, 13] (((appIT.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 13)) ⬝ₒ (.var 12)) (fun _ => K) [x0, x12, x13] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK4_beta (x0 x2 x11 x12 : Term) :
    WSteps (nockOK4 ⬝ x0 ⬝ x2 ⬝ x11 ⬝ x12) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x11)) ⬝ ((nockOK3 ⬝ x0) ⬝ x12)) := by
  have h := absNF_beta_close [0, 2, 11, 12] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 11))) ⬝ₒ ((nockOK3.toO ⬝ₒ .var 0) ⬝ₒ .var 12)) (fun _ => K) [x0, x2, x11, x12] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK5_beta (x0 x2 x10 x11 : Term) :
    WSteps (nockOK5 ⬝ x0 ⬝ x2 ⬝ x10 ⬝ x11) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x10)) ⬝ (((nockOK4 ⬝ x0) ⬝ x2) ⬝ x11)) := by
  have h := absNF_beta_close [0, 2, 10, 11] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 10))) ⬝ₒ (((nockOK4.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 11)) (fun _ => K) [x0, x2, x10, x11] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK6_beta (x16 x17 : Term) :
    WSteps (nockOK6 ⬝ x16 ⬝ x17) ((eqT ⬝ x16) ⬝ x17) := by
  have h := absNF_beta_close [16, 17] ((eqT.toO ⬝ₒ (.var 16)) ⬝ₒ (.var 17)) (fun _ => K) [x16, x17] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK7_beta (x0 x2 x15 x16 : Term) :
    WSteps (nockOK7 ⬝ x0 ⬝ x2 ⬝ x15 ⬝ x16) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x15)) ⬝ (nockOK6 ⬝ x16)) := by
  have h := absNF_beta_close [0, 2, 15, 16] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 15))) ⬝ₒ (nockOK6.toO ⬝ₒ .var 16)) (fun _ => K) [x0, x2, x15, x16] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK8_beta (x0 x2 x14 x15 : Term) :
    WSteps (nockOK8 ⬝ x0 ⬝ x2 ⬝ x14 ⬝ x15) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x14)) ⬝ (((nockOK7 ⬝ x0) ⬝ x2) ⬝ x15)) := by
  have h := absNF_beta_close [0, 2, 14, 15] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 14))) ⬝ₒ (((nockOK7.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 15)) (fun _ => K) [x0, x2, x14, x15] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK9_beta (x0 x2 x18 x20 x21 : Term) :
    WSteps (nockOK9 ⬝ x0 ⬝ x2 ⬝ x18 ⬝ x20 ⬝ x21) (((ifnT ⬝ ((x0 ⬝ x2) ⬝ x18)) ⬝ ((x0 ⬝ x2) ⬝ x20)) ⬝ ((x0 ⬝ x2) ⬝ x21)) := by
  have h := absNF_beta_close [0, 2, 18, 20, 21] (((ifnT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 18))) ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 20))) ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 21))) (fun _ => K) [x0, x2, x18, x20, x21] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK10_beta (x0 x2 x18 x19 : Term) :
    WSteps (nockOK10 ⬝ x0 ⬝ x2 ⬝ x18 ⬝ x19) ((cel2T ⬝ x19) ⬝ (((nockOK9 ⬝ x0) ⬝ x2) ⬝ x18)) := by
  have h := absNF_beta_close [0, 2, 18, 19] ((cel2T.toO ⬝ₒ (.var 19)) ⬝ₒ (((nockOK9.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 18)) (fun _ => K) [x0, x2, x18, x19] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK11_beta (x0 x23 x24 : Term) :
    WSteps (nockOK11 ⬝ x0 ⬝ x23 ⬝ x24) ((x0 ⬝ x24) ⬝ x23) := by
  have h := absNF_beta_close [0, 23, 24] (((.var 0) ⬝ₒ (.var 24)) ⬝ₒ (.var 23)) (fun _ => K) [x0, x23, x24] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK12_beta (x0 x2 x22 x23 : Term) :
    WSteps (nockOK12 ⬝ x0 ⬝ x2 ⬝ x22 ⬝ x23) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x22)) ⬝ ((nockOK11 ⬝ x0) ⬝ x23)) := by
  have h := absNF_beta_close [0, 2, 22, 23] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 22))) ⬝ₒ ((nockOK11.toO ⬝ₒ .var 0) ⬝ₒ .var 23)) (fun _ => K) [x0, x2, x22, x23] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK13_beta (x0 x2 x26 x27 : Term) :
    WSteps (nockOK13 ⬝ x0 ⬝ x2 ⬝ x26 ⬝ x27) ((x0 ⬝ ((CellC ⬝ x27) ⬝ x2)) ⬝ x26) := by
  have h := absNF_beta_close [0, 2, 26, 27] (((.var 0) ⬝ₒ ((CellC.toO ⬝ₒ (.var 27)) ⬝ₒ (.var 2))) ⬝ₒ (.var 26)) (fun _ => K) [x0, x2, x26, x27] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK14_beta (x0 x2 x25 x26 : Term) :
    WSteps (nockOK14 ⬝ x0 ⬝ x2 ⬝ x25 ⬝ x26) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x25)) ⬝ (((nockOK13 ⬝ x0) ⬝ x2) ⬝ x26)) := by
  have h := absNF_beta_close [0, 2, 25, 26] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 25))) ⬝ₒ (((nockOK13.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 26)) (fun _ => K) [x0, x2, x25, x26] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK15_beta (x0 x30 x31 : Term) :
    WSteps (nockOK15 ⬝ x0 ⬝ x30 ⬝ x31) (((appIT ⬝ x0) ⬝ ((slotBT ⬝ x31) ⬝ x30)) ⬝ x30) := by
  have h := absNF_beta_close [0, 30, 31] (((appIT.toO ⬝ₒ (.var 0)) ⬝ₒ ((slotBT.toO ⬝ₒ (.var 31)) ⬝ₒ (.var 30))) ⬝ₒ (.var 30)) (fun _ => K) [x0, x30, x31] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK16_beta (x32 x33 : Term) :
    WSteps (nockOK16 ⬝ x32 ⬝ x33) ErrC := by
  have h := absNF_beta_close [32, 33] ErrC.toO (fun _ => K) [x32, x33] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK17_beta (x34 x35 x36 : Term) :
    WSteps (nockOK17 ⬝ x34 ⬝ x35 ⬝ x36) ErrC := by
  have h := absNF_beta_close [34, 35, 36] ErrC.toO (fun _ => K) [x34, x35, x36] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK18_beta (x0 x28 x30 : Term) :
    WSteps (nockOK18 ⬝ x0 ⬝ x28 ⬝ x30) ((((x28 ⬝ ((nockOK15 ⬝ x0) ⬝ x30)) ⬝ nockOK16) ⬝ nockOK17) ⬝ ErrC) := by
  have h := absNF_beta_close [0, 28, 30] (((((.var 28) ⬝ₒ ((nockOK15.toO ⬝ₒ .var 0) ⬝ₒ .var 30)) ⬝ₒ nockOK16.toO) ⬝ₒ nockOK17.toO) ⬝ₒ ErrC.toO) (fun _ => K) [x0, x28, x30] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK19_beta (x0 x2 x28 x29 : Term) :
    WSteps (nockOK19 ⬝ x0 ⬝ x2 ⬝ x28 ⬝ x29) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x29)) ⬝ ((nockOK18 ⬝ x0) ⬝ x28)) := by
  have h := absNF_beta_close [0, 2, 28, 29] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 29))) ⬝ₒ ((nockOK18.toO ⬝ₒ .var 0) ⬝ₒ .var 28)) (fun _ => K) [x0, x2, x28, x29] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK20_beta (x41 x42 x43 : Term) :
    WSteps (nockOK20 ⬝ x41 ⬝ x42 ⬝ x43) (((editBT ⬝ x43) ⬝ x42) ⬝ x41) := by
  have h := absNF_beta_close [41, 42, 43] (((editBT.toO ⬝ₒ (.var 43)) ⬝ₒ (.var 42)) ⬝ₒ (.var 41)) (fun _ => K) [x41, x42, x43] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK21_beta (x44 x45 : Term) :
    WSteps (nockOK21 ⬝ x44 ⬝ x45) ErrC := by
  have h := absNF_beta_close [44, 45] ErrC.toO (fun _ => K) [x44, x45] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK22_beta (x46 x47 x48 : Term) :
    WSteps (nockOK22 ⬝ x46 ⬝ x47 ⬝ x48) ErrC := by
  have h := absNF_beta_close [46, 47, 48] ErrC.toO (fun _ => K) [x46, x47, x48] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK23_beta (x39 x41 x42 : Term) :
    WSteps (nockOK23 ⬝ x39 ⬝ x41 ⬝ x42) ((((x39 ⬝ ((nockOK20 ⬝ x41) ⬝ x42)) ⬝ nockOK21) ⬝ nockOK22) ⬝ ErrC) := by
  have h := absNF_beta_close [39, 41, 42] (((((.var 39) ⬝ₒ ((nockOK20.toO ⬝ₒ .var 41) ⬝ₒ .var 42)) ⬝ₒ nockOK21.toO) ⬝ₒ nockOK22.toO) ⬝ₒ ErrC.toO) (fun _ => K) [x39, x41, x42] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK24_beta (x0 x2 x39 x40 x41 : Term) :
    WSteps (nockOK24 ⬝ x0 ⬝ x2 ⬝ x39 ⬝ x40 ⬝ x41) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x40)) ⬝ ((nockOK23 ⬝ x39) ⬝ x41)) := by
  have h := absNF_beta_close [0, 2, 39, 40, 41] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 40))) ⬝ₒ ((nockOK23.toO ⬝ₒ .var 39) ⬝ₒ .var 41)) (fun _ => K) [x0, x2, x39, x40, x41] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK25_beta (x0 x2 x38 x39 x40 : Term) :
    WSteps (nockOK25 ⬝ x0 ⬝ x2 ⬝ x38 ⬝ x39 ⬝ x40) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x38)) ⬝ ((((nockOK24 ⬝ x0) ⬝ x2) ⬝ x39) ⬝ x40)) := by
  have h := absNF_beta_close [0, 2, 38, 39, 40] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 38))) ⬝ₒ ((((nockOK24.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 39) ⬝ₒ .var 40)) (fun _ => K) [x0, x2, x38, x39, x40] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK26_beta (x0 x2 x37 x38 : Term) :
    WSteps (nockOK26 ⬝ x0 ⬝ x2 ⬝ x37 ⬝ x38) ((cel2T ⬝ x37) ⬝ (((nockOK25 ⬝ x0) ⬝ x2) ⬝ x38)) := by
  have h := absNF_beta_close [0, 2, 37, 38] ((cel2T.toO ⬝ₒ (.var 37)) ⬝ₒ (((nockOK25.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 38)) (fun _ => K) [x0, x2, x37, x38] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK27_beta (x0 x2 x50 x51 : Term) :
    WSteps (nockOK27 ⬝ x0 ⬝ x2 ⬝ x50 ⬝ x51) ((x0 ⬝ x2) ⬝ x50) := by
  have h := absNF_beta_close [0, 2, 50, 51] (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 50)) (fun _ => K) [x0, x2, x50, x51] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK28_beta (x0 x2 x50 x54 : Term) :
    WSteps (nockOK28 ⬝ x0 ⬝ x2 ⬝ x50 ⬝ x54) ((x0 ⬝ x2) ⬝ x50) := by
  have h := absNF_beta_close [0, 2, 50, 54] (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 50)) (fun _ => K) [x0, x2, x50, x54] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK29_beta (x0 x2 x50 x52 x53 : Term) :
    WSteps (nockOK29 ⬝ x0 ⬝ x2 ⬝ x50 ⬝ x52 ⬝ x53) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x53)) ⬝ (((nockOK28 ⬝ x0) ⬝ x2) ⬝ x50)) := by
  have h := absNF_beta_close [0, 2, 50, 52, 53] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 53))) ⬝ₒ (((nockOK28.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)) (fun _ => K) [x0, x2, x50, x52, x53] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK30_beta (x0 x2 x50 x58 : Term) :
    WSteps (nockOK30 ⬝ x0 ⬝ x2 ⬝ x50 ⬝ x58) ((x0 ⬝ x2) ⬝ x50) := by
  have h := absNF_beta_close [0, 2, 50, 58] (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 50)) (fun _ => K) [x0, x2, x50, x58] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK31_beta (x0 x2 x50 x55 x56 x57 : Term) :
    WSteps (nockOK31 ⬝ x0 ⬝ x2 ⬝ x50 ⬝ x55 ⬝ x56 ⬝ x57) ((forceT ⬝ ((x0 ⬝ x2) ⬝ x56)) ⬝ (((nockOK30 ⬝ x0) ⬝ x2) ⬝ x50)) := by
  have h := absNF_beta_close [0, 2, 50, 55, 56, 57] ((forceT.toO ⬝ₒ (((.var 0) ⬝ₒ (.var 2)) ⬝ₒ (.var 56))) ⬝ₒ (((nockOK30.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)) (fun _ => K) [x0, x2, x50, x55, x56, x57] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockOK32_beta (x0 x2 x49 x50 : Term) :
    WSteps (nockOK32 ⬝ x0 ⬝ x2 ⬝ x49 ⬝ x50) ((((x49 ⬝ (((nockOK27 ⬝ x0) ⬝ x2) ⬝ x50)) ⬝ (((nockOK29 ⬝ x0) ⬝ x2) ⬝ x50)) ⬝ (((nockOK31 ⬝ x0) ⬝ x2) ⬝ x50)) ⬝ ErrC) := by
  have h := absNF_beta_close [0, 2, 49, 50] (((((.var 49) ⬝ₒ (((nockOK27.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)) ⬝ₒ (((nockOK29.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)) ⬝ₒ (((nockOK31.toO ⬝ₒ .var 0) ⬝ₒ .var 2) ⬝ₒ .var 50)) ⬝ₒ ErrC.toO) (fun _ => K) [x0, x2, x49, x50] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem decopK0_beta (x1 x2 : Term) :
    WSteps (decopK0 ⬝ x1 ⬝ x2) ((x1 ⬝ (decop1T ⬝ x2)) ⬝ (decop0T ⬝ x2)) := by
  have h := absNF_beta_close [1, 2] (((.var 1) ⬝ₒ (decop1T.toO ⬝ₒ (.var 2))) ⬝ₒ (decop0T.toO ⬝ₒ (.var 2))) (fun _ => K) [x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockPK0_beta (x0 x1 x3 x4 : Term) :
    WSteps (nockPK0 ⬝ x0 ⬝ x1 ⬝ x3 ⬝ x4) ((((nockOT ⬝ x0) ⬝ (decopT ⬝ x4)) ⬝ x1) ⬝ x3) := by
  have h := absNF_beta_close [0, 1, 3, 4] ((((nockOT.toO ⬝ₒ (.var 0)) ⬝ₒ (decopT.toO ⬝ₒ (.var 4))) ⬝ₒ (.var 1)) ⬝ₒ (.var 3)) (fun _ => K) [x0, x1, x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockPK1_beta (x0 x1 x2 x3 x5 x6 : Term) :
    WSteps (nockPK1 ⬝ x0 ⬝ x1 ⬝ x2 ⬝ x3 ⬝ x5 ⬝ x6) ((((autoconsT ⬝ x0) ⬝ x1) ⬝ x2) ⬝ x3) := by
  have h := absNF_beta_close [0, 1, 2, 3, 5, 6] ((((autoconsT.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 1)) ⬝ₒ (.var 2)) ⬝ₒ (.var 3)) (fun _ => K) [x0, x1, x2, x3, x5, x6] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockPK2_beta (x0 x1 x2 x3 x7 x8 x9 : Term) :
    WSteps (nockPK2 ⬝ x0 ⬝ x1 ⬝ x2 ⬝ x3 ⬝ x7 ⬝ x8 ⬝ x9) ((((autoconsT ⬝ x0) ⬝ x1) ⬝ x2) ⬝ x3) := by
  have h := absNF_beta_close [0, 1, 2, 3, 7, 8, 9] ((((autoconsT.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 1)) ⬝ₒ (.var 2)) ⬝ₒ (.var 3)) (fun _ => K) [x0, x1, x2, x3, x7, x8, x9] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockIK0_beta (x3 : Term) :
    WSteps (nockIK0 ⬝ x3) ErrC := by
  have h := absNF_beta_close [3] ErrC.toO (fun _ => K) [x3] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockIK1_beta (x0 x1 x4 x5 : Term) :
    WSteps (nockIK1 ⬝ x0 ⬝ x1 ⬝ x4 ⬝ x5) ((((nockPT ⬝ x0) ⬝ x1) ⬝ x4) ⬝ x5) := by
  have h := absNF_beta_close [0, 1, 4, 5] ((((nockPT.toO ⬝ₒ (.var 0)) ⬝ₒ (.var 1)) ⬝ₒ (.var 4)) ⬝ₒ (.var 5)) (fun _ => K) [x0, x1, x4, x5] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockIK2_beta (x1 x6 x7 x8 : Term) :
    WSteps (nockIK2 ⬝ x1 ⬝ x6 ⬝ x7 ⬝ x8) (x8 ⬝ x1) := by
  have h := absNF_beta_close [1, 6, 7, 8] ((.var 8) ⬝ₒ (.var 1)) (fun _ => K) [x1, x6, x7, x8] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem nockIG_beta (x0 x1 x2 : Term) :
    WSteps (nockIG ⬝ x0 ⬝ x1 ⬝ x2) ((((x2 ⬝ nockIK0) ⬝ ((nockIK1 ⬝ x0) ⬝ x1)) ⬝ (nockIK2 ⬝ x1)) ⬝ ErrC) := by
  have h := absNF_beta_close [0, 1, 2] (((((.var 2) ⬝ₒ nockIK0.toO) ⬝ₒ ((nockIK1.toO ⬝ₒ .var 0) ⬝ₒ .var 1)) ⬝ₒ (nockIK2.toO ⬝ₒ .var 1)) ⬝ₒ ErrC.toO) (fun _ => K) [x0, x1, x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appK0_beta (x2 : Term) :
    WSteps (appK0 ⬝ x2) ErrC := by
  have h := absNF_beta_close [2] ErrC.toO (fun _ => K) [x2] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appK1_beta (x0 x1 x3 x4 : Term) :
    WSteps (appK1 ⬝ x0 ⬝ x1 ⬝ x3 ⬝ x4) ((nockIT ⬝ x1) ⬝ x0) := by
  have h := absNF_beta_close [0, 1, 3, 4] ((nockIT.toO ⬝ₒ (.var 1)) ⬝ₒ (.var 0)) (fun _ => K) [x0, x1, x3, x4] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appK2_beta (x1 x5 x6 x7 : Term) :
    WSteps (appK2 ⬝ x1 ⬝ x5 ⬝ x6 ⬝ x7) (x7 ⬝ x1) := by
  have h := absNF_beta_close [1, 5, 6, 7] ((.var 7) ⬝ₒ (.var 1)) (fun _ => K) [x1, x5, x6, x7] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel0 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 0 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k0 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 0) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel1 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 1 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k1 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 1) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel2 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 2 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k2 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 2) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel3 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 3 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k3 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 3) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel4 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 4 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k4 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 4) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel5 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 5 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k5 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 5) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel6 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 6 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k6 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 6) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel7 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 7 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k7 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 7) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel8 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 8 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k8 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 8) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel9 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 9 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k9 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 9) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel10 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 10 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k10 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 10) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel11 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 11 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k11 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 11) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel12 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 12 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k12 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 12) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem opC_sel13 (k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 : Term) : WSteps (opC 13 ⬝ k0 ⬝ k1 ⬝ k2 ⬝ k3 ⬝ k4 ⬝ k5 ⬝ k6 ⬝ k7 ⬝ k8 ⬝ k9 ⬝ k10 ⬝ k11 ⬝ k12 ⬝ k13) k13 := by
  have h := absNF_beta_close [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] (.var 13) (fun _ => K) [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13] rfl
  simp only [_root_.appT, close_var, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

end Nock2Ski
