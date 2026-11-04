import Nock2Ski.DecBridge
import Ski.DecInd

open Nock
open Term
open Compose (boolT pairT)
open BitArith (bl nilT consT consO pairO wnf run)

/-!
# A continuation-passing normaliser for the `dec` jet's argument

lean-ski's `Ski/NoLayout.lean` proves that no closed term lays out a
computed `encNn` on the write-once machine: a computed cell reaches a
dynamic continuation only folded, as the thunk `K R w`.  lean-ski's
`Ski/DecInd.lean` gives the jet's row a reader that follows such thunks
(`DecJet.decRowI`).  This module gives the term that makes a computed
argument readable by it.

**`normT ⬝ x ⬝ k`** forces `x` (`x A C F E k`, the Scott cases carrying the
continuation `k` as an extra argument), normalises a cell's halves and an
atom's bits recursively, continuation-passing, and hands `k` the
normalised value.  Each value is built by straight-line code from the top
of the stack (`wrapT c n`: `S (K n) c z ⟶ n (c z)` writes the cell `c z`)
and delivered to the continuation below it as a `K`-thunk (`deliverT`:
`k` receives `K Q k`).  A cell's two halves come back in two
continuations; the tail's slot `K t` is folded over the head's
(`swapT`), so it reaches the wrapper as one thunk, the slot `DecJet.ktAt`
reads.  The recursion is Turing's fixpoint (`fixT`).

**`norm_enc`**: on any encoding `es` of a noun `s` (`Enc s es`, `Form`s
included), `normT ⬝ es ⬝ k ↠ k ⬝ encNoun s`.  So **`normJ_impl`**: for any
implementation `P` of lean-ski's contract, `normJ P = S normT (K P)`
implements it too, and **`normDec_enc`**: the normalised word `normJ
(nockToSki decF)` on any encoding of `s` reaches what the word reaches on
`encNoun s`, the encoded `decC s`.

That the machine's run of `normT` lays the value out as `decRowI` reads it
is what `bench/NockNorm.lean` measures (the term-level facts here do not
depend on it): in the compiled loop `while (top ≠ 0) dec` with every
occurrence of the word replaced by `normJ J`, the jet fires at every call.
-/

namespace Nock2Ski

namespace DecNorm

/-- `S (K n) c`: on `z`, write `c z` and continue with `n` on it. -/
def wrapT (c n : Term) : Term := S ⬝ (K ⬝ n) ⬝ c

/-- `S (K n)`: on `y z`, write `y z` and continue with `n` on it. -/
def ap2T (n : Term) : Term := S ⬝ (K ⬝ n)

/-- `S (K I)`: run `y` on `z`. -/
def runT : Term := S ⬝ (K ⬝ I)

/-- On `a b`: continue with `X` on `b (K a b)`, `a` folded as a thunk. -/
def swapT (X : Term) : Term := wrapT K (wrapT (S ⬝ X) runT)

/-- On `Q k`: `k (K Q k)`, `Q` handed over as a `K`-thunk. -/
def deliverT : Term := wrapT K (wrapT (S ⬝ I) runT)

def skkT : Term := S ⬝ (K ⬝ K)

/-- On `b k`: write `atomT b` and deliver it. -/
def buildAtomT : Term := wrapT K (wrapT (S ⬝ I) (wrapT skkT (wrapT skkT (wrapT skkT deliverT))))

/-- On `t k`: write `consT (boolT b) t` and deliver it. -/
def buildBitT (b : Bool) : Term := wrapT K (wrapT (S ⬝ (S ⬝ I ⬝ (K ⬝ boolT b))) (wrapT K deliverT))

/-- On `t H k`: write `cellT H t`, the tail slot folded over `H`, and
    deliver it. -/
def buildCellT : Term :=
  wrapT K (swapT (wrapT K (wrapT (S ⬝ I) (wrapT S (ap2T (wrapT skkT (wrapT skkT (wrapT K deliverT))))))))

/-- The empty bit list delivered: `k (K K k)`. -/
def nilHT : Term := S ⬝ I ⬝ (K ⬝ K)

/-- Turing's half: `[x y] y (x x y)`. -/
def thetaH : Term := S ⬝ (K ⬝ (S ⬝ I)) ⬝ (S ⬝ I ⬝ I)

/-- Turing's fixpoint. -/
def fixT (F : Term) : Term := thetaH ⬝ thetaH ⬝ F

-- The parts, open in the parts they call (`20` the bits' normaliser, `21`
-- the atom case, `22` the cell case's continuation, `23` the cell case,
-- `24` the form case, `25`, `26` the bit cases), so a symbolic run keeps
-- them whole.  Bound variables: `nb 0`, `t 1`, `k 2`, `b 3`, `bs 4`, `n 5`,
-- `h 6`, `h' 7`, `c 8`, `x 9`.

def v (i : Nat) : OTerm := .var i

/-- `λ nb t k. nb t (S (buildBitT b) (K k))`. -/
def bitCO (b : Bool) : OTerm := absN [0, 1, 2] (v 0 ⬝ₒ v 1 ⬝ₒ (.S ⬝ₒ (buildBitT b).toO ⬝ₒ (.K ⬝ₒ v 2)))

/-- `λ nb b. b (bitC true nb) (bitC false nb)`. -/
def consHO : OTerm := absN [0, 3] (v 3 ⬝ₒ (v 25 ⬝ₒ v 0) ⬝ₒ (v 26 ⬝ₒ v 0))

/-- `λ nb bs. bs nilH (consH nb)`. -/
def bitsBodyO : OTerm := absN [0, 4] (v 4 ⬝ₒ nilHT.toO ⬝ₒ (v 27 ⬝ₒ v 0))

/-- `λ n b k. normBits b (S buildAtom (K k))`. -/
def atomHO : OTerm := absN [5, 3, 2] (v 20 ⬝ₒ v 3 ⬝ₒ (.S ⬝ₒ buildAtomT.toO ⬝ₒ (.K ⬝ₒ v 2)))

/-- `λ n t k h'. n t (S (S buildCell (K h')) (K k))`. -/
def cellKO : OTerm :=
  absN [5, 1, 2, 7] (v 5 ⬝ₒ v 1 ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ buildCellT.toO ⬝ₒ (.K ⬝ₒ v 7)) ⬝ₒ (.K ⬝ₒ v 2)))

/-- `λ n h t k. n h (cellK n t k)`. -/
def cellHO : OTerm := absN [5, 6, 1, 2] (v 5 ⬝ₒ v 6 ⬝ₒ (v 22 ⬝ₒ v 5 ⬝ₒ v 1 ⬝ₒ v 2))

/-- `λ n h t c k. cellH n h t k`: a `Form` normalised as its cell. -/
def formHO : OTerm := absN [5, 6, 1, 8, 2] (v 23 ⬝ₒ v 5 ⬝ₒ v 6 ⬝ₒ v 1 ⬝ₒ v 2)

/-- `λ k. k errT` (no noun is `Err`). -/
def errHO : OTerm := absN [2] (v 2 ⬝ₒ errT.toO)

/-- `λ n x. x (atomH n) (cellH n) (formH n) errH`. -/
def normBodyO : OTerm := absN [5, 9] (v 9 ⬝ₒ (v 21 ⬝ₒ v 5) ⬝ₒ (v 23 ⬝ₒ v 5) ⬝ₒ (v 24 ⬝ₒ v 5) ⬝ₒ errHO)

def bitCT (b : Bool) : Term := (bitCO b).close (fun _ => K)
def consHT : Term := consHO.close (fun i => if i = 25 then bitCT true else bitCT false)
def bitsBodyT : Term := bitsBodyO.close (fun _ => consHT)

/-- **The bits' normaliser**: `normBits bs k ↠ k bs` on a bit list. -/
def normBitsT : Term := fixT bitsBodyT

def atomHT : Term := atomHO.close (fun _ => normBitsT)
def cellKT : Term := cellKO.close (fun _ => K)
def cellHT : Term := cellHO.close (fun _ => cellKT)
def formHT : Term := formHO.close (fun _ => cellHT)

/-- The parts the noun's body calls. -/
def σN : Nat → Term := fun i => if i = 21 then atomHT else if i = 23 then cellHT else formHT

def normBodyT : Term := normBodyO.close σN

/-- **The normaliser**: `normT x k ↠ k (encNoun s)` on an encoding `x` of
    `s`. -/
def normT : Term := fixT normBodyT

/-- **The normalised call**: `normJ P x ⟶ normT x (K P x)`, the jet `P`
    the continuation. -/
def normJ (P : Term) : Term := S ⬝ normT ⬝ (K ⬝ P)

-- ---------------------------------------------------------------------------
-- The parts, run symbolically
-- ---------------------------------------------------------------------------

theorem close_vars {t : OTerm} {σ₁ σ₂ : Nat → Term} (h : ∀ i ∈ t.vars, σ₁ i = σ₂ i) :
    t.close σ₁ = t.close σ₂ :=
  close_agree fun i hi => h i ((OTerm.mem_vars i t).1 (OTerm.mem_of_occ hi))

def a (i : Nat) : OTerm := .var i

/-- The closing environment of a symbolic run: the arguments at `0 … 9`,
    the parts at `20 …`. -/
def env (args : List Term) : Nat → Term := fun i =>
  if i = 20 then normBitsT else if i = 21 then atomHT else if i = 22 then cellKT else if i = 23 then cellHT
  else if i = 24 then formHT else if i = 25 then bitCT true else if i = 26 then bitCT false
  else if i = 27 then consHT else args.getD i K

theorem nilH_red (k : Term) : WSteps (nilHT ⬝ k) (k ⬝ K) := by
  have h := run (n := 20) (t := nilHT.toO ⬝ₒ a 0) (u := a 0 ⬝ₒ .K) (by decide +kernel) (env [k])
  simpa [OTerm.close, close_toO, a, env] using h

theorem bitK_red (b : Bool) (k t : Term) : WSteps (S ⬝ buildBitT b ⬝ (K ⬝ k) ⬝ t) (k ⬝ consT (boolT b) t) := by
  cases b
  · have h := run (n := 40) (t := .S ⬝ₒ (buildBitT false).toO ⬝ₒ (.K ⬝ₒ a 0) ⬝ₒ a 1)
      (u := a 0 ⬝ₒ consO (.K ⬝ₒ .I) (a 1)) (by decide +kernel) (env [k, t])
    simpa [OTerm.close, close_toO, a, env, BitArith.close_consO, boolT] using h
  · have h := run (n := 40) (t := .S ⬝ₒ (buildBitT true).toO ⬝ₒ (.K ⬝ₒ a 0) ⬝ₒ a 1)
      (u := a 0 ⬝ₒ consO .K (a 1)) (by decide +kernel) (env [k, t])
    simpa [OTerm.close, close_toO, a, env, BitArith.close_consO, boolT] using h

theorem atomK_red (k b : Term) : WSteps (S ⬝ buildAtomT ⬝ (K ⬝ k) ⬝ b) (k ⬝ atomT b) := by
  have h := run (n := 40) (t := .S ⬝ₒ buildAtomT.toO ⬝ₒ (.K ⬝ₒ a 0) ⬝ₒ a 1) (u := a 0 ⬝ₒ atomO (a 1))
    (by decide +kernel) (env [k, b])
  simpa [OTerm.close, close_toO, a, env, close_atomO] using h

theorem cellK_red (h k t : Term) : WSteps (S ⬝ (S ⬝ buildCellT ⬝ (K ⬝ h)) ⬝ (K ⬝ k) ⬝ t) (k ⬝ cellT h t) := by
  have e := run (n := 60) (t := .S ⬝ₒ (.S ⬝ₒ buildCellT.toO ⬝ₒ (.K ⬝ₒ a 0)) ⬝ₒ (.K ⬝ₒ a 1) ⬝ₒ a 2)
    (u := a 1 ⬝ₒ cellO (a 0) (a 2)) (by decide +kernel) (env [h, k, t])
  simpa [OTerm.close, close_toO, a, env, close_cellO] using e

theorem bitsBodyO_vars : bitsBodyO.vars = [27] := by decide +kernel
theorem consHO_vars : consHO.vars = [25, 26] := by decide +kernel
theorem atomHO_vars : atomHO.vars = [20] := by decide +kernel
theorem cellKO_vars : cellKO.vars = [] := by decide +kernel
theorem cellHO_vars : cellHO.vars = [22] := by decide +kernel
theorem formHO_vars : formHO.vars = [23] := by decide +kernel
theorem bitCO_vars (b : Bool) : (bitCO b).vars = [] := by cases b <;> decide +kernel
theorem normBodyO_vars : normBodyO.vars = [21, 23, 24] := by decide +kernel

theorem bitsBody_close (args : List Term) : bitsBodyO.close (env args) = bitsBodyT :=
  close_vars fun i hi => by rw [bitsBodyO_vars] at hi; simp at hi; subst hi; rfl
theorem consH_close (args : List Term) : consHO.close (env args) = consHT :=
  close_vars fun i hi => by rw [consHO_vars] at hi; simp at hi; rcases hi with rfl | rfl <;> rfl
theorem atomH_close (args : List Term) : atomHO.close (env args) = atomHT :=
  close_vars fun i hi => by rw [atomHO_vars] at hi; simp at hi; subst hi; rfl
theorem cellK_close (args : List Term) : cellKO.close (env args) = cellKT :=
  close_vars fun i hi => by rw [cellKO_vars] at hi; simp at hi
theorem cellH_close (args : List Term) : cellHO.close (env args) = cellHT :=
  close_vars fun i hi => by rw [cellHO_vars] at hi; simp at hi; subst hi; rfl
theorem formH_close (args : List Term) : formHO.close (env args) = formHT :=
  close_vars fun i hi => by rw [formHO_vars] at hi; simp at hi; subst hi; rfl
theorem bitC_close (b : Bool) (args : List Term) : (bitCO b).close (env args) = bitCT b :=
  close_vars fun i hi => by rw [bitCO_vars] at hi; simp at hi
theorem normBody_close (args : List Term) : normBodyO.close (env args) = normBodyT :=
  close_vars fun i hi => by
    rw [normBodyO_vars] at hi; simp at hi; rcases hi with rfl | rfl | rfl <;> rfl

theorem bitsBody_nil (nb k : Term) : WSteps (bitsBodyT ⬝ nb ⬝ K ⬝ k) (k ⬝ K) := by
  have h := run (n := 40) (t := bitsBodyO ⬝ₒ a 0 ⬝ₒ .K ⬝ₒ a 1) (u := a 1 ⬝ₒ .K) (by decide +kernel) (env [nb, k])
  simpa [OTerm.close, close_toO, a, env, bitsBody_close] using h

theorem bitsBody_cons (nb b t k : Term) : WSteps (bitsBodyT ⬝ nb ⬝ consT b t ⬝ k) (consHT ⬝ nb ⬝ b ⬝ t ⬝ k) := by
  have h := run (n := 40) (t := bitsBodyO ⬝ₒ a 0 ⬝ₒ consO (a 1) (a 2) ⬝ₒ a 3) (u := a 27 ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2 ⬝ₒ a 3)
    (by decide +kernel) (env [nb, b, t, k])
  simpa [OTerm.close, close_toO, a, env, bitsBody_close, BitArith.close_consO] using h

theorem consH_bit (b : Bool) (nb t k : Term) : WSteps (consHT ⬝ nb ⬝ boolT b ⬝ t ⬝ k) (bitCT b ⬝ nb ⬝ t ⬝ k) := by
  cases b
  · have h := run (n := 40) (t := consHO ⬝ₒ a 0 ⬝ₒ (.K ⬝ₒ .I) ⬝ₒ a 1 ⬝ₒ a 2) (u := a 26 ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2)
      (by decide +kernel) (env [nb, t, k])
    simpa [OTerm.close, close_toO, a, env, consH_close, boolT] using h
  · have h := run (n := 40) (t := consHO ⬝ₒ a 0 ⬝ₒ .K ⬝ₒ a 1 ⬝ₒ a 2) (u := a 25 ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2)
      (by decide +kernel) (env [nb, t, k])
    simpa [OTerm.close, close_toO, a, env, consH_close, boolT] using h

theorem bitC_red (b : Bool) (nb t k : Term) :
    WSteps (bitCT b ⬝ nb ⬝ t ⬝ k) (nb ⬝ t ⬝ (S ⬝ buildBitT b ⬝ (K ⬝ k))) := by
  cases b
  · have h := run (n := 40) (t := bitCO false ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2)
      (u := a 0 ⬝ₒ a 1 ⬝ₒ (.S ⬝ₒ (buildBitT false).toO ⬝ₒ (.K ⬝ₒ a 2))) (by decide +kernel) (env [nb, t, k])
    simpa [OTerm.close, close_toO, a, env, bitC_close] using h
  · have h := run (n := 40) (t := bitCO true ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2)
      (u := a 0 ⬝ₒ a 1 ⬝ₒ (.S ⬝ₒ (buildBitT true).toO ⬝ₒ (.K ⬝ₒ a 2))) (by decide +kernel) (env [nb, t, k])
    simpa [OTerm.close, close_toO, a, env, bitC_close] using h

theorem body_atom (n b k : Term) : WSteps (normBodyT ⬝ n ⬝ atomT b ⬝ k) (atomHT ⬝ n ⬝ b ⬝ k) := by
  have h := run (n := 40) (t := normBodyO ⬝ₒ a 0 ⬝ₒ atomO (a 1) ⬝ₒ a 2) (u := a 21 ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2)
    (by decide +kernel) (env [n, b, k])
  simpa [OTerm.close, close_toO, a, env, normBody_close, close_atomO] using h

theorem body_cell (n h t k : Term) : WSteps (normBodyT ⬝ n ⬝ cellT h t ⬝ k) (cellHT ⬝ n ⬝ h ⬝ t ⬝ k) := by
  have e := run (n := 40) (t := normBodyO ⬝ₒ a 0 ⬝ₒ cellO (a 1) (a 2) ⬝ₒ a 3) (u := a 23 ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2 ⬝ₒ a 3)
    (by decide +kernel) (env [n, h, t, k])
  simpa [OTerm.close, close_toO, a, env, normBody_close, close_cellO] using e

theorem body_form (n h t c k : Term) :
    WSteps (normBodyT ⬝ n ⬝ formT h t c ⬝ k) (formHT ⬝ n ⬝ h ⬝ t ⬝ c ⬝ k) := by
  have e := run (n := 40) (t := normBodyO ⬝ₒ a 0 ⬝ₒ formO (a 1) (a 2) (a 3) ⬝ₒ a 4)
    (u := a 24 ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2 ⬝ₒ a 3 ⬝ₒ a 4) (by decide +kernel) (env [n, h, t, c, k])
  simpa [OTerm.close, close_toO, a, env, normBody_close, close_formO] using e

theorem atomH_red (n b k : Term) : WSteps (atomHT ⬝ n ⬝ b ⬝ k) (normBitsT ⬝ b ⬝ (S ⬝ buildAtomT ⬝ (K ⬝ k))) := by
  have h := run (n := 40) (t := atomHO ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2) (u := a 20 ⬝ₒ a 1 ⬝ₒ (.S ⬝ₒ buildAtomT.toO ⬝ₒ (.K ⬝ₒ a 2)))
    (by decide +kernel) (env [n, b, k])
  simpa [OTerm.close, close_toO, a, env, atomH_close] using h

theorem cellH_red (n h t k : Term) : WSteps (cellHT ⬝ n ⬝ h ⬝ t ⬝ k) (n ⬝ h ⬝ (cellKT ⬝ n ⬝ t ⬝ k)) := by
  have e := run (n := 40) (t := cellHO ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2 ⬝ₒ a 3) (u := a 0 ⬝ₒ a 1 ⬝ₒ (a 22 ⬝ₒ a 0 ⬝ₒ a 2 ⬝ₒ a 3))
    (by decide +kernel) (env [n, h, t, k])
  simpa [OTerm.close, close_toO, a, env, cellH_close] using e

theorem cellKT_red (n t k h' : Term) :
    WSteps (cellKT ⬝ n ⬝ t ⬝ k ⬝ h') (n ⬝ t ⬝ (S ⬝ (S ⬝ buildCellT ⬝ (K ⬝ h')) ⬝ (K ⬝ k))) := by
  have e := run (n := 40) (t := cellKO ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2 ⬝ₒ a 3)
    (u := a 0 ⬝ₒ a 1 ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ buildCellT.toO ⬝ₒ (.K ⬝ₒ a 3)) ⬝ₒ (.K ⬝ₒ a 2))) (by decide +kernel) (env [n, t, k, h'])
  simpa [OTerm.close, close_toO, a, env, cellK_close] using e

theorem formH_red (n h t c k : Term) : WSteps (formHT ⬝ n ⬝ h ⬝ t ⬝ c ⬝ k) (cellHT ⬝ n ⬝ h ⬝ t ⬝ k) := by
  have e := run (n := 40) (t := formHO ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2 ⬝ₒ a 3 ⬝ₒ a 4) (u := a 23 ⬝ₒ a 0 ⬝ₒ a 1 ⬝ₒ a 2 ⬝ₒ a 4)
    (by decide +kernel) (env [n, h, t, c, k])
  simpa [OTerm.close, close_toO, a, env, formH_close] using e

/-- **Turing's fixpoint unrolls**: `fixT F ↠ F (fixT F)`. -/
theorem fix_red (F : Term) : WSteps (fixT F) (F ⬝ fixT F) := by
  -- `H H F ⟶ K (S I) H (S I I H) F ⟶ S I (S I I H) F ⟶ I F (S I I H F) ⟶ F (S I I H F)`
  have h1 : WSteps (fixT F) (F ⬝ (S ⬝ I ⬝ I ⬝ thetaH ⬝ F)) :=
    (WSteps.left F (WSteps.single (.S _ _ _))).trans
      ((WSteps.left F (WSteps.left _ (WSteps.single (.K _ _)))).trans
        ((WSteps.single (.S _ _ _)).trans ((WSteps.left _ (WSteps.single (.I _))))))
  -- `S I I H ⟶ I H (I H) ⟶ H (I H) ⟶ H H`
  have h2 : WSteps (S ⬝ I ⬝ I ⬝ thetaH) (thetaH ⬝ thetaH) :=
    (WSteps.single (.S _ _ _)).trans ((WSteps.left _ (WSteps.single (.I _))).trans
      (WSteps.right _ (WSteps.single (.I _))))
  exact h1.trans (WSteps.right F (WSteps.left F h2))

-- ---------------------------------------------------------------------------
-- The normaliser's specification
-- ---------------------------------------------------------------------------

/-- **The bits' normaliser**: on a bit list, it hands the continuation the
    same list. -/
theorem normBits_bl : ∀ (bs : List Bool) (k : Term), WSteps (normBitsT ⬝ bl bs ⬝ k) (k ⬝ bl bs)
  | [], k => (WSteps.left _ (WSteps.left _ (fix_red bitsBodyT))).trans (bitsBody_nil _ k)
  | b :: bs, k => by
    have h1 := (WSteps.left _ (WSteps.left _ (fix_red bitsBodyT))).trans (bitsBody_cons normBitsT (boolT b) (bl bs) k)
    have h2 := (consH_bit b normBitsT (bl bs) k).trans (bitC_red b normBitsT (bl bs) k)
    have h3 := normBits_bl bs (S ⬝ buildBitT b ⬝ (K ⬝ k))
    exact h1.trans (h2.trans (h3.trans (bitK_red b k (bl bs))))

/-- **`norm_enc`: the normaliser on any encoding** of a noun hands its
    continuation the noun's code-free encoding. -/
theorem norm_enc {s : Noun} {es : Term} (he : Enc s es) : ∀ k, WSteps (normT ⬝ es ⬝ k) (k ⬝ encNoun s) := by
  induction he with
  | atom n =>
    intro k
    have h1 := (WSteps.left _ (WSteps.left _ (fix_red normBodyT))).trans (body_atom normT (bitsT (bits n)) k)
    exact h1.trans ((atomH_red _ _ _).trans ((normBits_bl _ _).trans (atomK_red k _)))
  | @cell h t eh et _ _ ihh iht =>
    intro k
    have h1 := (WSteps.left _ (WSteps.left _ (fix_red normBodyT))).trans (body_cell normT eh et k)
    have h2 := (cellH_red normT eh et k).trans (ihh (cellKT ⬝ normT ⬝ et ⬝ k))
    have h3 := (cellKT_red normT et k (encNoun h)).trans (iht _)
    exact h1.trans (h2.trans (h3.trans (cellK_red (encNoun h) k (encNoun t))))
  | @form h t eh et _ _ ihh iht =>
    intro k
    have h1 := (WSteps.left _ (WSteps.left _ (fix_red normBodyT))).trans (body_form normT eh et (nockToSki (.cell h t)) k)
    have h2 := (formH_red normT eh et (nockToSki (.cell h t)) k).trans ((cellH_red normT eh et k).trans (ihh (cellKT ⬝ normT ⬝ et ⬝ k)))
    have h3 := (cellKT_red normT et k (encNoun h)).trans (iht _)
    exact h1.trans (h2.trans (h3.trans (cellK_red (encNoun h) k (encNoun t))))

/-- **The normalised call implements the contract**: for any implementation
    `P` of lean-ski's `dec` contract, `normJ P = S normT (K P)` is one. -/
theorem normJ_impl {P : Term} (hP : DataJet.Implements DecJet.decContract P) :
    DataJet.Implements DecJet.decContract (normJ P) := fun s => by
  show WSteps (normJ P ⬝ DecJet.encNn s.1) _
  have e := encNn_eq s.2.1
  have h1 : WSteps (normJ P ⬝ DecJet.encNn s.1) (normT ⬝ DecJet.encNn s.1 ⬝ (K ⬝ P ⬝ DecJet.encNn s.1)) :=
    .single (.S _ _ _)
  rw [e] at h1 ⊢
  have h2 := norm_enc (enc_encNoun (toNoun s.1)) (K ⬝ P ⬝ encNoun (toNoun s.1))
  have h3 : WSteps (K ⬝ P ⬝ encNoun (toNoun s.1) ⬝ encNoun (toNoun s.1)) (P ⬝ encNoun (toNoun s.1)) :=
    WSteps.left _ (.single (.K _ _))
  have h4 := hP s
  rw [show DecJet.decContract.encI s = DecJet.encNn s.1 from rfl, e] at h4
  exact h1.trans (h2.trans (h3.trans h4))

/-- **The normalised word on any encoding**: `normJ (nockToSki decF)`
    reaches on any encoding of `S` what the word reaches on `encNoun S`,
    the encoded `decC S`. -/
theorem normDec_enc {s : Noun} {es : Term} (he : Enc s es) :
    WSteps (normJ (nockToSki decF) ⬝ es) (encOut (decC s)) := by
  have h1 : WSteps (normJ (nockToSki decF) ⬝ es) (normT ⬝ es ⬝ (K ⬝ nockToSki decF ⬝ es)) := .single (.S _ _ _)
  have h2 := norm_enc he (K ⬝ nockToSki decF ⬝ es)
  have h3 : WSteps (K ⬝ nockToSki decF ⬝ es ⬝ encNoun s) (nockToSki decF ⬝ encNoun s) :=
    WSteps.left _ (.single (.K _ _))
  exact h1.trans (h2.trans (h3.trans (decF_bare s)))

end DecNorm

end Nock2Ski
