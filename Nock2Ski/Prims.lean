import Nock2Ski.Noun
import Nock2Ski.Decls

open Nock
open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

/-!
# The primitives, read from the compiler's own terms

Milestone M1 of `PLAN.md`, §2.1 and §8: `nock.ski`'s primitives `hd tl cel
force inc eq ifn` (and the recursive helpers `incbk eqb eqn` and `loob`)
as closed SKI terms, **identical to the terms SKIjack emits**, with their
specifications over `encNoun` proved by weak reduction.  `app`, M1's
twelfth equation, now names the interpreter `nockI` and lives in
`Interp.lean` (M3); its pin and specs are there (`app_cell`, `app_form`).

## The Front verdict

`nockSrc` (`Decls.lean`) is the text of `python/skinock/nock.ski` as
committed plus the compiler's default for opcode 12.  `Front.compileFile`
**refuses this file** (`compileFile_refuses`): its generation pass
`Front.generate` (`generate.py`'s `find_object_type`) takes `noun` for an
object type, because `Cell noun noun` is a constructor with two fields of
its own type, and then refuses it because `Atom bits` and `Form noun noun
noun` beside it are not leaves.  skijack's own `find_object_type` raises
on the same shape; skinock compiles the file with `skijack.compile(src,
generate_forms=False)`, which skips that pass.  Lexing and parsing succeed
(`parse_pin`), so `nockFile` compiles the file the same way:
`Front.parseFile` and then `Front.compileDecls`, the pipeline of
`Front.compileFile` without `Front.generate`.  Every term below is pinned
to that output by `decide +kernel` (`hd_pin`, …, `ifn_pin`, and the eight
constructors), through `nockFileD`, the compilation of the parsed
declarations, so that the kernel does not parse the file at each pin;
`terms/*.ski`, the terms the Python pipeline printed, agree with them
character for character (`scripts/lean-check.sh` does not re-check this;
`Front` is the reference).

## The terms

Each equation is written as `Src`, the source after case lowering
(`Ski/Compile.lean`): a case is the scrutinee applied to one continuation
per constructor in declaration order, each the λ over the branch's
binders; the λs are lifted and bracket-abstracted by `comp`, a recursive
equation is Curry's `Y` (`Ycomb`) over the abstraction with the
self-reference first (`compRec`).  A recursive function used by another
(`eqb` in `eqn`, `incbk` in `inc`, `loob` and `eqn` in `eq`) is a variable
`30`–`33` in the open generator (`eqnGO`, `incGO`, `eqGO`) and the closed
term is that generator closed with the dependency (`eqnG`, `incT`, `eqT`):
the same term skijack emits with the dependency inlined, and the form a
symbolic run can stop at.

## The proofs

Each spec is a run of the open term that the kernel checks (`wnf`, `run`,
as `Ski/BitArith.lean`), closed with the actual arguments, and for the
recursive functions an induction on bits or nouns whose hypothesis closes
the self-reference.  `Y F` unrolls to `yfix F = ω ω` with `ω = S (K F) (S I
I)` (`Ycomb_unroll`), and `yfix F ↠ F (yfix F)` (`yfix_unroll`), so the
specs are stated for `yfix` and transferred to the compiled `Y F`.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- The source and its compilation
-- ---------------------------------------------------------------------------

/-- `Front.compileFile` refuses it: `noun` has the object type's shape with
    non-leaf constructors beside the application. -/
theorem compileFile_refuses : (Front.compileFile nockSrc).isNone = true := by decide +kernel

-- ---------------------------------------------------------------------------
-- The equations, lowered
-- ---------------------------------------------------------------------------

/-- A variable. -/
def v (n : Nat) : Src := .var n
/-- A global, a closed term. -/
def g (t : Term) : Src := .glob t
/-- A λ. -/
def sl (x : Nat) (b : Src) : Src := .lam x b

/-- `hd n = n |> { Atom b Err ; Cell h t h ; Form h t c h ; Err Err }` -/
def hdSrc : Src :=
  (v 0) ⬝ₛ (sl 1 (g ErrC)) ⬝ₛ (sl 2 (sl 3 (v 2))) ⬝ₛ (sl 4 (sl 5 (sl 6 (v 4)))) ⬝ₛ (g ErrC)

/-- `tl n = n |> { Atom b Err ; Cell h t t ; Form h t c t ; Err Err }` -/
def tlSrc : Src :=
  (v 0) ⬝ₛ (sl 1 (g ErrC)) ⬝ₛ (sl 2 (sl 3 (v 3))) ⬝ₛ (sl 4 (sl 5 (sl 6 (v 5)))) ⬝ₛ (g ErrC)

/-- `force x k = x |> { Atom b (k (Atom b)) ; Cell h t (k (Cell h t)) ;
    Form h t c (k (Form h t c)) ; Err Err }` -/
def forceSrc : Src :=
  (v 0) ⬝ₛ (sl 2 ((v 1) ⬝ₛ ((g AtomC) ⬝ₛ (v 2))))
    ⬝ₛ (sl 3 (sl 4 ((v 1) ⬝ₛ ((g CellC) ⬝ₛ (v 3) ⬝ₛ (v 4)))))
    ⬝ₛ (sl 5 (sl 6 (sl 7 ((v 1) ⬝ₛ ((g FormC) ⬝ₛ (v 5) ⬝ₛ (v 6) ⬝ₛ (v 7)))))) ⬝ₛ (g ErrC)

/-- `cel n = n |> { Atom b (Atom (Cons T Nil)) ; Cell h t (Atom Nil) ;
    Form h t c (Atom Nil) ; Err Err }` -/
def celSrc : Src :=
  (v 0) ⬝ₛ (sl 1 ((g AtomC) ⬝ₛ ((g ConsC) ⬝ₛ (g TC) ⬝ₛ (g NilC))))
    ⬝ₛ (sl 2 (sl 3 ((g AtomC) ⬝ₛ (g NilC))))
    ⬝ₛ (sl 4 (sl 5 (sl 6 ((g AtomC) ⬝ₛ (g NilC))))) ⬝ₛ (g ErrC)

/-- `incbk b k = b |> { Nil (k (Cons T Nil)) ; Cons x r (x |> { T (incbk r
    (\r2. k (Cons F r2))) ; F (k (Cons T r)) }) }`; `incbk` itself is `0`. -/
def incbkSrc : Src :=
  (v 1) ⬝ₛ ((v 2) ⬝ₛ ((g ConsC) ⬝ₛ (g TC) ⬝ₛ (g NilC)))
    ⬝ₛ (sl 3 (sl 4 ((v 3) ⬝ₛ ((v 0) ⬝ₛ (v 4) ⬝ₛ (sl 5 ((v 2) ⬝ₛ ((g ConsC) ⬝ₛ (g FC) ⬝ₛ (v 5)))))
                          ⬝ₛ ((v 2) ⬝ₛ ((g ConsC) ⬝ₛ (g TC) ⬝ₛ (v 4))))))

/-- `inc n = n |> { Atom b (incbk b (\b2. Atom b2)) ; Cell h t Err ;
    Form h t c Err ; Err Err }`, over the term for `incbk`. -/
def incSrc (incbk : Src) : Src :=
  (v 0) ⬝ₛ (sl 1 (incbk ⬝ₛ (v 1) ⬝ₛ (sl 2 ((g AtomC) ⬝ₛ (v 2)))))
    ⬝ₛ (sl 3 (sl 4 (g ErrC))) ⬝ₛ (sl 5 (sl 6 (sl 7 (g ErrC)))) ⬝ₛ (g ErrC)

/-- `eqb a b = a |> { Nil (b |> { Nil T ; Cons y s F }) ; Cons x r (b |> {
    Nil F ; Cons y s (x |> { T (y |> { T (eqb r s) ; F F }) ; F (y |> { T F ;
    F (eqb r s) }) }) }) }`; `eqb` itself is `0`. -/
def eqbSrc : Src :=
  (v 1) ⬝ₛ ((v 2) ⬝ₛ (g TC) ⬝ₛ (sl 3 (sl 4 (g FC))))
    ⬝ₛ (sl 5 (sl 6 ((v 2) ⬝ₛ (g FC)
         ⬝ₛ (sl 7 (sl 8 ((v 5) ⬝ₛ ((v 7) ⬝ₛ ((v 0) ⬝ₛ (v 6) ⬝ₛ (v 8)) ⬝ₛ (g FC))
                             ⬝ₛ ((v 7) ⬝ₛ (g FC) ⬝ₛ ((v 0) ⬝ₛ (v 6) ⬝ₛ (v 8)))))))))

/-- `eqn a b = a |> { Atom p (b |> { Atom q (eqb p q) ; Cell h t F ;
    Form h t c F ; Err F }) ; Cell h t (b |> { Atom q F ; Cell h2 t2 ((eqn h h2)
    |> { T (eqn t t2) ; F F }) ; Form h2 t2 c ((eqn h h2) |> { T (eqn t t2) ;
    F F }) ; Err F }) ; Form h t c (b |> { … the same … }) ; Err F }`;
    `eqn` itself is `0`, over the term for `eqb`. -/
def eqnSrc (eqb : Src) : Src :=
  (v 1)
    ⬝ₛ (sl 3 ((v 2) ⬝ₛ (sl 4 (eqb ⬝ₛ (v 3) ⬝ₛ (v 4))) ⬝ₛ (sl 5 (sl 6 (g FC)))
                    ⬝ₛ (sl 7 (sl 8 (sl 9 (g FC)))) ⬝ₛ (g FC)))
    ⬝ₛ (sl 10 (sl 11 ((v 2) ⬝ₛ (sl 12 (g FC))
          ⬝ₛ (sl 13 (sl 14 ((v 0) ⬝ₛ (v 10) ⬝ₛ (v 13) ⬝ₛ ((v 0) ⬝ₛ (v 11) ⬝ₛ (v 14)) ⬝ₛ (g FC))))
          ⬝ₛ (sl 15 (sl 16 (sl 17 ((v 0) ⬝ₛ (v 10) ⬝ₛ (v 15) ⬝ₛ ((v 0) ⬝ₛ (v 11) ⬝ₛ (v 16)) ⬝ₛ (g FC)))))
          ⬝ₛ (g FC))))
    ⬝ₛ (sl 18 (sl 19 (sl 20 ((v 2) ⬝ₛ (sl 21 (g FC))
          ⬝ₛ (sl 22 (sl 23 ((v 0) ⬝ₛ (v 18) ⬝ₛ (v 22) ⬝ₛ ((v 0) ⬝ₛ (v 19) ⬝ₛ (v 23)) ⬝ₛ (g FC))))
          ⬝ₛ (sl 24 (sl 25 (sl 26 ((v 0) ⬝ₛ (v 18) ⬝ₛ (v 24) ⬝ₛ ((v 0) ⬝ₛ (v 19) ⬝ₛ (v 25)) ⬝ₛ (g FC)))))
          ⬝ₛ (g FC)))))
    ⬝ₛ (g FC)

/-- `loob x = x |> { T (Atom Nil) ; F (Atom (Cons T Nil)) }` -/
def loobSrc : Src :=
  (v 0) ⬝ₛ ((g AtomC) ⬝ₛ (g NilC)) ⬝ₛ ((g AtomC) ⬝ₛ ((g ConsC) ⬝ₛ (g TC) ⬝ₛ (g NilC)))

/-- `eq a b = loob (eqn a b)`, over the terms for `loob` and `eqn`. -/
def eqSrc (loob eqn : Src) : Src := loob ⬝ₛ (eqn ⬝ₛ (v 0) ⬝ₛ (v 1))

/-- `ifn c y n = c |> { Atom b (b |> { Nil y ; Cons x r (r |> { Nil (x |> { T n
    ; F Err }) ; Cons z q Err }) }) ; Cell h t Err ; Form h t c Err ; Err Err }` -/
def ifnSrc : Src :=
  (v 0)
    ⬝ₛ (sl 3 ((v 3) ⬝ₛ (v 1) ⬝ₛ (sl 4 (sl 5 ((v 5) ⬝ₛ ((v 4) ⬝ₛ (v 2) ⬝ₛ (g ErrC))
                                                 ⬝ₛ (sl 6 (sl 7 (g ErrC))))))))
    ⬝ₛ (sl 8 (sl 9 (g ErrC))) ⬝ₛ (sl 10 (sl 11 (sl 12 (g ErrC)))) ⬝ₛ (g ErrC)

-- ---------------------------------------------------------------------------
-- The terms
-- ---------------------------------------------------------------------------

def hdT : Term := toTerm (compDef [0] hdSrc)
def tlT : Term := toTerm (compDef [0] tlSrc)
def forceT : Term := toTerm (compDef [0, 1] forceSrc)
def celT : Term := toTerm (compDef [0] celSrc)

/-- `incbk`'s generator: the abstraction over `incbk` itself, `b` and `k`. -/
def incbkG : Term := toTerm (absN [0, 1, 2] (comp [0, 1, 2] incbkSrc))
/-- `incbk = Y incbkG`. -/
def incbkT : Term := Ycomb ⬝ incbkG
theorem incbkT_eq : incbkT = toTerm (compRec 0 [1, 2] incbkSrc) := rfl

/-- `inc` with `incbk` the variable `31`. -/
def incGO : OTerm := absN [0] (comp [0] (incSrc (v 31)))
def incT : Term := incGO.close (updC (fun _ => K) 31 incbkT)

def eqbG : Term := toTerm (absN [0, 1, 2] (comp [0, 1, 2] eqbSrc))
def eqbT : Term := Ycomb ⬝ eqbG
theorem eqbT_eq : eqbT = toTerm (compRec 0 [1, 2] eqbSrc) := rfl

/-- `eqn`'s generator with `eqb` the variable `30`. -/
def eqnGO : OTerm := absN [0, 1, 2] (comp [0, 1, 2] (eqnSrc (v 30)))
def eqnG : Term := eqnGO.close (updC (fun _ => K) 30 eqbT)
def eqnT : Term := Ycomb ⬝ eqnG

def loobT : Term := toTerm (compDef [0] loobSrc)

/-- `eq` with `loob` the variable `32` and `eqn` the variable `33`. -/
def eqGO : OTerm := absN [0, 1] (comp [0, 1] (eqSrc (v 32) (v 33)))
def eqT : Term := eqGO.close (updC (updC (fun _ => K) 32 loobT) 33 eqnT)

def ifnT : Term := toTerm (compDef [0, 1, 2] ifnSrc)

-- ---------------------------------------------------------------------------
-- The terms are the compiler's
-- ---------------------------------------------------------------------------

theorem T_pin : Front.termOf nockFile (nm! "T") = some TC := by
  rw [nockFile_eq]; decide +kernel
theorem F_pin : Front.termOf nockFile (nm! "F") = some FC := by
  rw [nockFile_eq]; decide +kernel
theorem Nil_pin : Front.termOf nockFile (nm! "Nil") = some NilC := by
  rw [nockFile_eq]; decide +kernel
theorem Cons_pin : Front.termOf nockFile (nm! "Cons") = some ConsC := by
  rw [nockFile_eq]; decide +kernel
theorem Atom_pin : Front.termOf nockFile (nm! "Atom") = some AtomC := by
  rw [nockFile_eq]; decide +kernel
theorem Cell_pin : Front.termOf nockFile (nm! "Cell") = some CellC := by
  rw [nockFile_eq]; decide +kernel
theorem Form_pin : Front.termOf nockFile (nm! "Form") = some FormC := by
  rw [nockFile_eq]; decide +kernel
theorem Err_pin : Front.termOf nockFile (nm! "Err") = some ErrC := by
  rw [nockFile_eq]; decide +kernel

theorem hd_pin : Front.termOf nockFile (nm! "hd") = some hdT := by
  rw [nockFile_eq]; decide +kernel
theorem tl_pin : Front.termOf nockFile (nm! "tl") = some tlT := by
  rw [nockFile_eq]; decide +kernel
theorem force_pin : Front.termOf nockFile (nm! "force") = some forceT := by
  rw [nockFile_eq]; decide +kernel
theorem cel_pin : Front.termOf nockFile (nm! "cel") = some celT := by
  rw [nockFile_eq]; decide +kernel
theorem incbk_pin : Front.termOf nockFile (nm! "incbk") = some incbkT := by
  rw [nockFile_eq]; decide +kernel
theorem inc_pin : Front.termOf nockFile (nm! "inc") = some incT := by
  rw [nockFile_eq]; decide +kernel
theorem eqb_pin : Front.termOf nockFile (nm! "eqb") = some eqbT := by
  rw [nockFile_eq]; decide +kernel
theorem eqn_pin : Front.termOf nockFile (nm! "eqn") = some eqnT := by
  rw [nockFile_eq]; decide +kernel
theorem loob_pin : Front.termOf nockFile (nm! "loob") = some loobT := by
  rw [nockFile_eq]; decide +kernel
theorem eq_pin : Front.termOf nockFile (nm! "eq") = some eqT := by
  rw [nockFile_eq]; decide +kernel
theorem ifn_pin : Front.termOf nockFile (nm! "ifn") = some ifnT := by
  rw [nockFile_eq]; decide +kernel

-- ---------------------------------------------------------------------------
-- Curry's Y, as skijack emits it
-- ---------------------------------------------------------------------------

/-- `ω_F = λx. F (x x) = S (K F) (S I I)`. -/
def yω (F : Term) : Term := S ⬝ (K ⬝ F) ⬝ (S ⬝ I ⬝ I)

/-- `ω_F ω_F`, the fixed point `Y F` reaches. -/
def yfix (F : Term) : Term := yω F ⬝ yω F

theorem yW_red (F : Term) :
    WSteps (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ F) (yω F) :=
  .step (.S _ _ _) (.step (.left _ (.S _ _ _))
    (.step (.left _ (.left _ (.K _ _))) (.single (.right _ (.K _ _)))))

/-- `Y F ↠ ω_F ω_F`. -/
theorem Ycomb_unroll (F : Term) : WSteps (Ycomb ⬝ F) (yfix F) := by
  unfold Ycomb
  exact .step (.S _ _ _) (.step (.left _ (.K _ _)) (.step (.S _ _ _)
    (.step (.left _ (.I _)) (.step (.right _ (.I _)) (WSteps.app (yW_red F) (yW_red F))))))

/-- `ω_F ω_F ↠ F (ω_F ω_F)`. -/
theorem yfix_unroll (F : Term) : WSteps (yfix F) (F ⬝ yfix F) := by
  show WSteps (S ⬝ (K ⬝ F) ⬝ (S ⬝ I ⬝ I) ⬝ yω F) (F ⬝ (yω F ⬝ yω F))
  exact .step (.S _ _ _) (.step (.left _ (.K _ _)) (.step (.right _ (.S _ _ _))
    (.step (.right _ (.left _ (.I _))) (.single (.right _ (.right _ (.I _)))))))

def incbkFix : Term := yfix incbkG
def eqbFix : Term := yfix eqbG
def eqnFix : Term := yfix eqnG

theorem incbk_unfold (b k : Term) :
    WSteps (incbkFix ⬝ b ⬝ k) (incbkG ⬝ incbkFix ⬝ b ⬝ k) :=
  WSteps.left _ (WSteps.left _ (yfix_unroll _))

theorem eqb_unfold (a b : Term) : WSteps (eqbFix ⬝ a ⬝ b) (eqbG ⬝ eqbFix ⬝ a ⬝ b) :=
  WSteps.left _ (WSteps.left _ (yfix_unroll _))

theorem eqn_unfold (a b : Term) : WSteps (eqnFix ⬝ a ⬝ b) (eqnG ⬝ eqnFix ⬝ a ⬝ b) :=
  WSteps.left _ (WSteps.left _ (yfix_unroll _))

-- ---------------------------------------------------------------------------
-- Closing the open generators
-- ---------------------------------------------------------------------------

/-- Two closings that agree on a term's variables close it the same. -/
theorem close_of_vars {t : OTerm} {σ₁ σ₂ : Nat → Term} (h : ∀ i ∈ t.vars, σ₁ i = σ₂ i) :
    t.close σ₁ = t.close σ₂ :=
  close_agree fun i hi => h i ((OTerm.mem_vars i t).mp (OTerm.mem_of_occ hi))

theorem eqnGO_vars : eqnGO.vars = [30] := by decide +kernel
theorem incGO_vars : incGO.vars = [31] := by decide +kernel
theorem eqGO_vars : eqGO.vars = [32, 33] := by decide +kernel

theorem eqnGO_close (σ : Nat → Term) (h : σ 30 = eqbT) : eqnGO.close σ = eqnG :=
  close_of_vars fun i hi => by
    rw [eqnGO_vars, List.mem_singleton] at hi
    subst hi
    rw [h]; rfl

theorem incGO_close (σ : Nat → Term) (h : σ 31 = incbkT) : incGO.close σ = incT :=
  close_of_vars fun i hi => by
    rw [incGO_vars, List.mem_singleton] at hi
    subst hi
    rw [h]; rfl

theorem eqGO_close (σ : Nat → Term) (h32 : σ 32 = loobT) (h33 : σ 33 = eqnT) :
    eqGO.close σ = eqT :=
  close_of_vars fun i hi => by
    rw [eqGO_vars, List.mem_cons, List.mem_singleton] at hi
    rcases hi with rfl | rfl
    · rw [h32]; rfl
    · rw [h33]; rfl

/-- The dependencies of the open generators. -/
def depEnv : Nat → Term := fun i =>
  if i = 30 then eqbT else if i = 31 then incbkT else if i = 32 then loobT
  else if i = 33 then eqnT else K

/-- The environment of a symbolic run: variable `10 + i` is the `i`-th term,
    variables `30`–`33` the dependencies. -/
def envR (ts : List Term) : Nat → Term := fun i => if i < 30 then ts.getD (i - 10) K else depEnv i

-- ---------------------------------------------------------------------------
-- hd, tl
-- ---------------------------------------------------------------------------

theorem hd_atom_run : wnf 100 (hdT.toO ⬝ₒ atomO (.var 11)) = errO := by decide +kernel
theorem hd_cell_run : wnf 100 (hdT.toO ⬝ₒ cellO (.var 11) (.var 12)) = .var 11 := by decide +kernel
theorem hd_form_run : wnf 100 (hdT.toO ⬝ₒ formO (.var 11) (.var 12) (.var 13)) = .var 11 := by
  decide +kernel
theorem hd_err_run : wnf 100 (hdT.toO ⬝ₒ errO) = errO := by decide +kernel
theorem tl_atom_run : wnf 100 (tlT.toO ⬝ₒ atomO (.var 11)) = errO := by decide +kernel
theorem tl_cell_run : wnf 100 (tlT.toO ⬝ₒ cellO (.var 11) (.var 12)) = .var 12 := by decide +kernel
theorem tl_form_run : wnf 100 (tlT.toO ⬝ₒ formO (.var 11) (.var 12) (.var 13)) = .var 12 := by
  decide +kernel
theorem tl_err_run : wnf 100 (tlT.toO ⬝ₒ errO) = errO := by decide +kernel

/-- **`hd`**: the head of a cell. -/
theorem hd_spec (h t : Noun) : WSteps (hdT ⬝ encNoun (.cell h t)) (encNoun h) := by
  have e := run hd_cell_run (envR [K, encNoun h, encNoun t])
  simp only [OTerm.close, close_toO, close_cellO] at e
  exact e

theorem hd_atom (n : Nat) : WSteps (hdT ⬝ encNoun (.atom n)) errT := by
  have e := run hd_atom_run (envR [K, bitsT (bits n)])
  simp only [OTerm.close, close_toO, close_atomO, close_errO] at e
  exact e

theorem hd_form (h t c : Term) : WSteps (hdT ⬝ formT h t c) h := by
  have e := run hd_form_run (envR [K, h, t, c])
  simp only [OTerm.close, close_toO, close_formO] at e
  exact e

theorem hd_err : WSteps (hdT ⬝ errT) errT := by
  have e := run hd_err_run (fun _ => K)
  simp only [OTerm.close, close_toO, close_errO] at e
  exact e

/-- **`tl`**: the tail of a cell. -/
theorem tl_spec (h t : Noun) : WSteps (tlT ⬝ encNoun (.cell h t)) (encNoun t) := by
  have e := run tl_cell_run (envR [K, encNoun h, encNoun t])
  simp only [OTerm.close, close_toO, close_cellO] at e
  exact e

theorem tl_atom (n : Nat) : WSteps (tlT ⬝ encNoun (.atom n)) errT := by
  have e := run tl_atom_run (envR [K, bitsT (bits n)])
  simp only [OTerm.close, close_toO, close_atomO, close_errO] at e
  exact e

theorem tl_form (h t c : Term) : WSteps (tlT ⬝ formT h t c) t := by
  have e := run tl_form_run (envR [K, h, t, c])
  simp only [OTerm.close, close_toO, close_formO] at e
  exact e

theorem tl_err : WSteps (tlT ⬝ errT) errT := by
  have e := run tl_err_run (fun _ => K)
  simp only [OTerm.close, close_toO, close_errO] at e
  exact e

-- ---------------------------------------------------------------------------
-- cel: Nock's `?`
-- ---------------------------------------------------------------------------

theorem bits_zero : bits 0 = [] := by simp [bits]
theorem bits_one : bits 1 = [true] := by rw [bits_pos (by omega)]; simp [bits]

theorem cel_atom_run : wnf 100 (celT.toO ⬝ₒ atomO (.var 11)) = atomO (consO ttO .K) := by
  decide +kernel
theorem cel_cell_run : wnf 100 (celT.toO ⬝ₒ cellO (.var 11) (.var 12)) = atomO .K := by
  decide +kernel
theorem cel_form_run : wnf 100 (celT.toO ⬝ₒ formO (.var 11) (.var 12) (.var 13)) = atomO .K := by
  decide +kernel
theorem cel_err_run : wnf 100 (celT.toO ⬝ₒ errO) = errO := by decide +kernel

/-- **`cel`** is `wut`: `0` on a cell, `1` on an atom. -/
theorem cel_spec (n : Noun) : WSteps (celT ⬝ encNoun n) (encNoun (wut n)) := by
  cases n with
  | atom m =>
    have e := run cel_atom_run (envR [K, bitsT (bits m)])
    simp only [OTerm.close, close_toO, close_atomO, BitArith.close_consO, close_ttO] at e
    show WSteps _ (encNoun (.atom 1))
    rw [encNoun_atom 1, bits_one]
    exact e
  | cell h t =>
    have e := run cel_cell_run (envR [K, encNoun h, encNoun t])
    simp only [OTerm.close, close_toO, close_cellO, close_atomO] at e
    show WSteps _ (encNoun (.atom 0))
    rw [encNoun_atom 0, bits_zero]
    exact e

theorem cel_form (h t c : Term) : WSteps (celT ⬝ formT h t c) (encNoun (.atom 0)) := by
  have e := run cel_form_run (envR [K, h, t, c])
  simp only [OTerm.close, close_toO, close_formO, close_atomO] at e
  rw [encNoun_atom, bits_zero]
  exact e

theorem cel_err : WSteps (celT ⬝ errT) errT := by
  have e := run cel_err_run (fun _ => K)
  simp only [OTerm.close, close_toO, close_errO] at e
  exact e

-- ---------------------------------------------------------------------------
-- force
-- ---------------------------------------------------------------------------

theorem force_atom_run : wnf 100 (forceT.toO ⬝ₒ atomO (.var 11) ⬝ₒ .var 12) =
    .var 12 ⬝ₒ atomO (.var 11) := by decide +kernel
theorem force_cell_run : wnf 100 (forceT.toO ⬝ₒ cellO (.var 11) (.var 12) ⬝ₒ .var 13) =
    .var 13 ⬝ₒ cellO (.var 11) (.var 12) := by decide +kernel
theorem force_form_run :
    wnf 100 (forceT.toO ⬝ₒ formO (.var 11) (.var 12) (.var 13) ⬝ₒ .var 14) =
      .var 14 ⬝ₒ formO (.var 11) (.var 12) (.var 13) := by decide +kernel
theorem force_err_run : wnf 100 (forceT.toO ⬝ₒ errO ⬝ₒ .var 14) = errO := by decide +kernel

/-- **`force`** hands a value to its continuation. -/
theorem force_spec (n : Noun) (k : Term) : WSteps (forceT ⬝ encNoun n ⬝ k) (k ⬝ encNoun n) := by
  cases n with
  | atom m =>
    have e := run force_atom_run (envR [K, bitsT (bits m), k])
    simp only [OTerm.close, close_toO, close_atomO] at e
    exact e
  | cell h t =>
    have e := run force_cell_run (envR [K, encNoun h, encNoun t, k])
    simp only [OTerm.close, close_toO, close_cellO] at e
    exact e

theorem force_form (h t c k : Term) : WSteps (forceT ⬝ formT h t c ⬝ k) (k ⬝ formT h t c) := by
  have e := run force_form_run (envR [K, h, t, c, k])
  simp only [OTerm.close, close_toO, close_formO] at e
  exact e

/-- `force` propagates a crash. -/
theorem force_err (k : Term) : WSteps (forceT ⬝ errT ⬝ k) errT := by
  have e := run force_err_run (envR [K, K, K, K, k])
  simp only [OTerm.close, close_toO, close_errO] at e
  exact e

-- ---------------------------------------------------------------------------
-- inc: Nock's `+`
-- ---------------------------------------------------------------------------

/-- The continuation `incbk` passes down on a `T` bit, `\r2. k (Cons F r2)`
    lifted over `k`, as it stands after one unfolding. -/
def incKO (k : OTerm) : OTerm :=
  .S ⬝ₒ (.K ⬝ₒ k) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))))) ⬝ₒ .K))
def incKT (k : Term) : Term :=
  S ⬝ (K ⬝ k) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ (K ⬝ I))))) ⬝ K))
theorem close_incKO (σ : Nat → Term) (k : OTerm) : (incKO k).close σ = incKT (k.close σ) := rfl

theorem incK_run : wnf 50 (incKO (.var 12) ⬝ₒ .var 13) = .var 12 ⬝ₒ consO ffO (.var 13) := by
  decide +kernel

theorem incK_red (k y : Term) : WSteps (incKT k ⬝ y) (k ⬝ consT (boolT false) y) := by
  have e := run incK_run (envR [K, K, k, y])
  simp only [OTerm.close, close_incKO, BitArith.close_consO, close_ffO] at e
  exact e

theorem incbk_nil_run : wnf 100 (incbkG.toO ⬝ₒ .var 10 ⬝ₒ .K ⬝ₒ .var 12) =
    .var 12 ⬝ₒ consO ttO .K := by decide +kernel
theorem incbk_T_run : wnf 100 (incbkG.toO ⬝ₒ .var 10 ⬝ₒ consO ttO (.var 11) ⬝ₒ .var 12) =
    .var 10 ⬝ₒ .var 11 ⬝ₒ incKO (.var 12) := by decide +kernel
theorem incbk_F_run : wnf 100 (incbkG.toO ⬝ₒ .var 10 ⬝ₒ consO ffO (.var 11) ⬝ₒ .var 12) =
    .var 12 ⬝ₒ consO ttO (.var 11) := by decide +kernel

/-- **`incbk`** increments bits and hands them to its continuation. -/
theorem incbk_spec : ∀ (bs : List Bool) (k : Term),
    WSteps (incbkFix ⬝ bitsT bs ⬝ k) (k ⬝ bitsT (incB bs))
  | [], k => by
    have e := run incbk_nil_run (envR [incbkFix, K, k])
    simp only [OTerm.close, close_toO, BitArith.close_consO, close_ttO] at e
    exact (incbk_unfold _ _).trans e
  | true :: bs, k => by
    have e := run incbk_T_run (envR [incbkFix, bitsT bs, k])
    simp only [OTerm.close, close_toO, BitArith.close_consO, close_ttO, close_incKO] at e
    exact (incbk_unfold _ _).trans (e.trans ((incbk_spec bs (incKT k)).trans (incK_red _ _)))
  | false :: bs, k => by
    have e := run incbk_F_run (envR [incbkFix, bitsT bs, k])
    simp only [OTerm.close, close_toO, BitArith.close_consO, close_ttO, close_ffO] at e
    exact (incbk_unfold _ _).trans e

theorem inc_atom_run : wnf 100 (incGO ⬝ₒ atomO (.var 11)) = .var 31 ⬝ₒ .var 11 ⬝ₒ AtomC.toO := by
  decide +kernel
theorem inc_cell_run : wnf 100 (incGO ⬝ₒ cellO (.var 11) (.var 12)) = errO := by decide +kernel
theorem inc_form_run : wnf 100 (incGO ⬝ₒ formO (.var 11) (.var 12) (.var 13)) = errO := by
  decide +kernel
theorem inc_err_run : wnf 100 (incGO ⬝ₒ errO) = errO := by decide +kernel

/-- **`inc`** is `+ 1` on atoms. -/
theorem inc_spec (n : Nat) : WSteps (incT ⬝ encNoun (.atom n)) (encNoun (.atom (n + 1))) := by
  have e := run inc_atom_run (envR [K, bitsT (bits n)])
  simp only [OTerm.close, close_toO, close_atomO] at e
  rw [incGO_close _ rfl] at e
  rw [encNoun_atom, encNoun_atom, ← incB_bits]
  exact e.trans ((WSteps.left _ (WSteps.left _ (Ycomb_unroll incbkG))).trans
    ((incbk_spec _ _).trans (AtomC_red _)))

/-- **`inc` crashes on a cell.** -/
theorem inc_cell (h t : Noun) : WSteps (incT ⬝ encNoun (.cell h t)) errT := by
  have e := run inc_cell_run (envR [K, encNoun h, encNoun t])
  simp only [OTerm.close, close_cellO, close_errO] at e
  rw [incGO_close _ rfl] at e
  exact e

theorem inc_form (h t c : Term) : WSteps (incT ⬝ formT h t c) errT := by
  have e := run inc_form_run (envR [K, h, t, c])
  simp only [OTerm.close, close_formO, close_errO] at e
  rw [incGO_close _ rfl] at e
  exact e

theorem inc_err : WSteps (incT ⬝ errT) errT := by
  have e := run inc_err_run (envR [])
  simp only [OTerm.close, close_errO] at e
  rw [incGO_close _ rfl] at e
  exact e

-- ---------------------------------------------------------------------------
-- eq: Nock's `=`
-- ---------------------------------------------------------------------------

theorem eqb_nn_run : wnf 100 (eqbG.toO ⬝ₒ .var 10 ⬝ₒ .K ⬝ₒ .K) = .K := by decide +kernel
theorem eqb_nc_run : wnf 100 (eqbG.toO ⬝ₒ .var 10 ⬝ₒ .K ⬝ₒ consO (.var 13) (.var 12)) = .K ⬝ₒ .I := by
  decide +kernel
theorem eqb_cn_run : wnf 100 (eqbG.toO ⬝ₒ .var 10 ⬝ₒ consO (.var 13) (.var 11) ⬝ₒ .K) = .K ⬝ₒ .I := by
  decide +kernel
theorem eqb_cc_run : ∀ x y : Bool,
    wnf 100 (eqbG.toO ⬝ₒ .var 10 ⬝ₒ consO (boolT x).toO (.var 11) ⬝ₒ consO (boolT y).toO (.var 12)) =
      if x = y then .var 10 ⬝ₒ .var 11 ⬝ₒ .var 12 else .K ⬝ₒ .I := by
  decide +kernel

/-- **`eqb`** is equality of bit lists. -/
theorem eqb_spec : ∀ xs ys : List Bool,
    WSteps (eqbFix ⬝ bitsT xs ⬝ bitsT ys) (boolT (decide (xs = ys)))
  | [], [] => by
    have e := run eqb_nn_run (envR [eqbFix])
    simp only [OTerm.close, close_toO] at e
    exact (eqb_unfold _ _).trans e
  | [], y :: ys => by
    have e := run eqb_nc_run (envR [eqbFix, K, bitsT ys, boolT y])
    simp only [OTerm.close, close_toO, BitArith.close_consO] at e
    rw [show decide (([] : List Bool) = y :: ys) = false by simp]
    exact (eqb_unfold _ _).trans e
  | x :: xs, [] => by
    have e := run eqb_cn_run (envR [eqbFix, bitsT xs, K, boolT x])
    simp only [OTerm.close, close_toO, BitArith.close_consO] at e
    rw [show decide (x :: xs = ([] : List Bool)) = false by simp]
    exact (eqb_unfold _ _).trans e
  | x :: xs, y :: ys => by
    have r := eqb_cc_run x y
    by_cases hxy : x = y
    · rw [if_pos hxy] at r
      have e := run r (envR [eqbFix, bitsT xs, bitsT ys])
      simp only [OTerm.close, close_toO, BitArith.close_consO] at e
      rw [show decide (x :: xs = y :: ys) = decide (xs = ys) by simp [hxy]]
      exact (eqb_unfold _ _).trans (e.trans (eqb_spec xs ys))
    · rw [if_neg hxy] at r
      have e := run r (envR [eqbFix, bitsT xs, bitsT ys])
      simp only [OTerm.close, close_toO, BitArith.close_consO] at e
      rw [show decide (x :: xs = y :: ys) = false by simp [hxy]]
      exact (eqb_unfold _ _).trans e

theorem eqn_aa_run : wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ atomO (.var 11) ⬝ₒ atomO (.var 12)) =
    .var 30 ⬝ₒ .var 11 ⬝ₒ .var 12 := by decide +kernel
theorem eqn_ac_run : wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ atomO (.var 11) ⬝ₒ cellO (.var 12) (.var 13)) =
    .K ⬝ₒ .I := by decide +kernel
theorem eqn_ca_run : wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ cellO (.var 11) (.var 12) ⬝ₒ atomO (.var 13)) =
    .K ⬝ₒ .I := by decide +kernel
theorem eqn_cc_run :
    wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ cellO (.var 11) (.var 12) ⬝ₒ cellO (.var 13) (.var 14)) =
      .var 10 ⬝ₒ .var 11 ⬝ₒ .var 13 ⬝ₒ (.var 10 ⬝ₒ .var 12 ⬝ₒ .var 14) ⬝ₒ ffO := by
  decide +kernel

/-- **`eqn`** is structural equality of nouns, a Scott Boolean. -/
theorem eqn_spec : ∀ a b : Noun, WSteps (eqnFix ⬝ encNoun a ⬝ encNoun b) (boolT (decide (a = b)))
  | .atom m, .atom n => by
    have e := run eqn_aa_run (envR [eqnFix, bitsT (bits m), bitsT (bits n)])
    simp only [OTerm.close, close_atomO] at e
    rw [eqnGO_close _ rfl] at e
    rw [show decide (Noun.atom m = Noun.atom n) = decide (bits m = bits n) by
      simp [bits_eq_iff]]
    exact (eqn_unfold _ _).trans (e.trans
      ((WSteps.left _ (WSteps.left _ (Ycomb_unroll eqbG))).trans (eqb_spec _ _)))
  | .atom m, .cell h t => by
    have e := run eqn_ac_run (envR [eqnFix, bitsT (bits m), encNoun h, encNoun t])
    simp only [OTerm.close, close_atomO, close_cellO] at e
    rw [eqnGO_close _ rfl] at e
    rw [show decide (Noun.atom m = Noun.cell h t) = false by simp]
    exact (eqn_unfold _ _).trans e
  | .cell h t, .atom n => by
    have e := run eqn_ca_run (envR [eqnFix, encNoun h, encNoun t, bitsT (bits n)])
    simp only [OTerm.close, close_atomO, close_cellO] at e
    rw [eqnGO_close _ rfl] at e
    rw [show decide (Noun.cell h t = Noun.atom n) = false by simp]
    exact (eqn_unfold _ _).trans e
  | .cell h t, .cell h2 t2 => by
    have e := run eqn_cc_run (envR [eqnFix, encNoun h, encNoun t, encNoun h2, encNoun t2])
    simp only [OTerm.close, close_cellO, close_ffO] at e
    rw [eqnGO_close _ rfl] at e
    rw [show decide (Noun.cell h t = Noun.cell h2 t2) = (decide (h = h2) && decide (t = t2)) by
      simp]
    refine (eqn_unfold _ _).trans (e.trans ((WSteps.left _ (WSteps.left _ (eqn_spec h h2))).trans
      ((Compose.boolT_sel _ _ _).trans ?_)))
    cases decide (h = h2)
    · exact .refl _
    · exact eqn_spec t t2

theorem eq_run : wnf 100 (eqGO ⬝ₒ .var 11 ⬝ₒ .var 12) = .var 32 ⬝ₒ (.var 33 ⬝ₒ .var 11 ⬝ₒ .var 12) := by
  decide +kernel
theorem loob_T_run : wnf 100 (loobT.toO ⬝ₒ .K) = atomO .K := by decide +kernel
theorem loob_F_run : wnf 100 (loobT.toO ⬝ₒ (.K ⬝ₒ .I)) = atomO (consO ttO .K) := by decide +kernel

/-- **`loob`**: a Scott Boolean to a loobean, `0` for yes. -/
theorem loob_spec (b : Bool) : WSteps (loobT ⬝ boolT b) (encNoun (.atom (if b then 0 else 1))) := by
  cases b with
  | true =>
    have e := run loob_T_run (fun _ => K)
    simp only [OTerm.close, close_toO, close_atomO] at e
    show WSteps _ (encNoun (.atom 0))
    rw [encNoun_atom, bits_zero]
    exact e
  | false =>
    have e := run loob_F_run (fun _ => K)
    simp only [OTerm.close, close_toO, close_atomO, BitArith.close_consO, close_ttO] at e
    show WSteps _ (encNoun (.atom 1))
    rw [encNoun_atom, bits_one]
    exact e

/-- **`eq`** is Nock's `=`: `0` on equal nouns, `1` otherwise (`tisN`). -/
theorem eq_spec (a b : Noun) :
    WSteps (eqT ⬝ encNoun a ⬝ encNoun b) (encNoun (.atom (if a = b then 0 else 1))) := by
  have e := run eq_run (envR [K, encNoun a, encNoun b])
  simp only [OTerm.close] at e
  rw [eqGO_close _ rfl rfl] at e
  refine e.trans ((WSteps.right _ ((WSteps.left _ (WSteps.left _ (Ycomb_unroll eqnG))).trans
    (eqn_spec a b))).trans ?_)
  by_cases hab : a = b
  · rw [if_pos hab, decide_eq_true hab]; exact loob_spec true
  · rw [if_neg hab, decide_eq_false hab]; exact loob_spec false

theorem eq_tisN (a b : Noun) : WSteps (eqT ⬝ encNoun a ⬝ encNoun b) (encNoun (tisN a b)) := by
  have e := eq_spec a b
  unfold tisN
  by_cases h : a = b
  · rw [if_pos h]; rw [if_pos h] at e; exact e
  · rw [if_neg h]; rw [if_neg h] at e; exact e

-- ---------------------------------------------------------------------------
-- ifn: Nock's `6`, the test
-- ---------------------------------------------------------------------------

theorem ifn_zero_run : wnf 100 (ifnT.toO ⬝ₒ atomO .K ⬝ₒ .var 12 ⬝ₒ .var 13) = .var 12 := by
  decide +kernel
theorem ifn_one_run : wnf 100 (ifnT.toO ⬝ₒ atomO (consO ttO .K) ⬝ₒ .var 12 ⬝ₒ .var 13) = .var 13 := by
  decide +kernel
theorem ifn_big_run :
    wnf 100 (ifnT.toO ⬝ₒ atomO (consO (.var 15) (consO (.var 16) (.var 17))) ⬝ₒ .var 12 ⬝ₒ .var 13) =
      errO := by decide +kernel
theorem ifn_cell_run : wnf 100 (ifnT.toO ⬝ₒ cellO (.var 11) (.var 14) ⬝ₒ .var 12 ⬝ₒ .var 13) = errO := by
  decide +kernel
theorem ifn_form_run :
    wnf 100 (ifnT.toO ⬝ₒ formO (.var 11) (.var 14) (.var 15) ⬝ₒ .var 12 ⬝ₒ .var 13) = errO := by
  decide +kernel
theorem ifn_err_run : wnf 100 (ifnT.toO ⬝ₒ errO ⬝ₒ .var 12 ⬝ₒ .var 13) = errO := by decide +kernel

/-- **`ifn`** on `0` takes the first branch. -/
theorem ifn_zero (y n : Term) : WSteps (ifnT ⬝ encNoun (.atom 0) ⬝ y ⬝ n) y := by
  have e := run ifn_zero_run (envR [K, K, y, n])
  simp only [OTerm.close, close_toO, close_atomO] at e
  rw [encNoun_atom, bits_zero]
  exact e

/-- **`ifn`** on `1` takes the second. -/
theorem ifn_one (y n : Term) : WSteps (ifnT ⬝ encNoun (.atom 1) ⬝ y ⬝ n) n := by
  have e := run ifn_one_run (envR [K, K, y, n])
  simp only [OTerm.close, close_toO, close_atomO, BitArith.close_consO, close_ttO] at e
  rw [encNoun_atom, bits_one]
  exact e

/-- **`ifn`** crashes on any other atom. -/
theorem ifn_big {m : Nat} (hm : 2 ≤ m) (y n : Term) : WSteps (ifnT ⬝ encNoun (.atom m) ⬝ y ⬝ n) errT := by
  obtain ⟨b, c, r, hb⟩ := bits_two hm
  have e := run ifn_big_run (envR [K, K, y, n, K, boolT b, boolT c, bitsT r])
  simp only [OTerm.close, close_toO, close_atomO, BitArith.close_consO, close_errO] at e
  rw [encNoun_atom, hb]
  exact e

/-- **`ifn`** crashes on a cell. -/
theorem ifn_cell (h t : Noun) (y n : Term) : WSteps (ifnT ⬝ encNoun (.cell h t) ⬝ y ⬝ n) errT := by
  have e := run ifn_cell_run (envR [K, encNoun h, y, n, encNoun t])
  simp only [OTerm.close, close_toO, close_cellO, close_errO] at e
  exact e

theorem ifn_form (h t c y n : Term) : WSteps (ifnT ⬝ formT h t c ⬝ y ⬝ n) errT := by
  have e := run ifn_form_run (envR [K, h, y, n, t, c])
  simp only [OTerm.close, close_toO, close_formO, close_errO] at e
  exact e

theorem ifn_err (y n : Term) : WSteps (ifnT ⬝ errT ⬝ y ⬝ n) errT := by
  have e := run ifn_err_run (envR [K, K, y, n])
  simp only [OTerm.close, close_toO, close_errO] at e
  exact e

-- ---------------------------------------------------------------------------
-- Tagged axis pulls: Nock's `/` over the sum, as the compiler emits axes
-- ---------------------------------------------------------------------------

/-- The subtree along a path, `false` the head and `true` the tail; Nock's
    slot at axis `n ≥ 1` is `slot x (Front.axisSteps n)`.  Into an atom is
    a crash, `none`. -/
def slot : Noun → List Bool → Option Noun
  | x, [] => some x
  | .cell l _, false :: bs => slot l bs
  | .cell _ r, true :: bs => slot r bs
  | .atom _, _ :: _ => none
termination_by structural _ bs => bs

/-- The pull along a path with the tagged projections, the first step
    innermost, as `Front.pickC` builds an axis. -/
def pickT (e : Term) : List Bool → Term
  | [] => e
  | b :: bs => pickT ((if b then tlT else hdT) ⬝ e) bs

/-- Axis `n` of `e`, `n ≥ 1`: the chain of `hd` and `tl` its binary digits
    spell, over the tagged sum (`Ski/Door.lean`'s `pull`, with `hdT`/`tlT`). -/
def pullT (n : Nat) (e : Term) : Term := pickT e (Front.axisSteps n)

theorem pickT_cong {e e' : Term} (h : WSteps e e') :
    ∀ bs, WSteps (pickT e bs) (pickT e' bs)
  | [] => h
  | _ :: bs => pickT_cong (WSteps.right _ h) bs

/-- **The tagged pull is the slot**: along any path the noun has, the pull of
    a term reducing to the noun reduces to the encoded subtree. -/
theorem pick_tagged : ∀ (bs : List Bool) (x y : Noun) (e : Term),
    slot x bs = some y → WSteps e (encNoun x) → WSteps (pickT e bs) (encNoun y)
  | [], x, y, e, h, he => by
    obtain rfl : x = y := by simpa [slot] using h
    exact he
  | false :: bs, .cell l r, y, e, h, he =>
    pick_tagged bs l y _ h ((WSteps.right _ he).trans (hd_spec _ _))
  | true :: bs, .cell l r, y, e, h, he =>
    pick_tagged bs r y _ h ((WSteps.right _ he).trans (tl_spec _ _))
  | _ :: _, .atom _, _, _, h, _ => by simp [slot] at h

/-- Axis `n` of `x`, when Nock's slot has it. -/
theorem pull_tagged {n : Nat} {x y : Noun} (h : slot x (Front.axisSteps n) = some y) :
    WSteps (pullT n (encNoun x)) (encNoun y) :=
  pick_tagged _ x y _ h (.refl _)

/-- Axes 2 and 7 of `[[a b] [c d]]`. -/
theorem pull_two (a b c d : Noun) :
    WSteps (pullT 2 (encNoun (.cell (.cell a b) (.cell c d)))) (encNoun (.cell a b)) :=
  pull_tagged (y := .cell a b) rfl

theorem pull_seven (a b c d : Noun) :
    WSteps (pullT 7 (encNoun (.cell (.cell a b) (.cell c d)))) (encNoun d) :=
  pull_tagged (y := d) rfl

end Nock2Ski
