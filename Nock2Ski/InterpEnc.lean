import Nock2Ski.Enc

open Nock
open Term
open Compose (boolT)

/-!
# The interpreter over `Enc`

Milestone M3 of `PLAN.md`: the specifications of `nock.ski`'s interpreter
fallback over the encoding relation `Enc` (`Nock2Ski/Enc.lean`), the
pieces the simulation (`Nock2Ski/Embed.lean`) assembles.

- The dispatch: `nockI s f` on an atom crashes, on a `Cell h t` goes to
  `nockP` with the halves, on a `Form` runs the code (`nockI_atom`,
  `nockI_cell`, `nockI_form`); `nockP` reads an atom head's opcode
  (`nockP_atom`) and treats a cell head as an autocons (`nockP_cell`);
  `appI` is `app` with the evaluator passed in (`appI_cell`, `appI_form`);
  `cel2` splits an encoded cell (`cel2_enc`) and crashes on an atom
  (`cel2_atom`).
- `interp_op`: on a plain cell `[k t]` with `k ≤ 12` the interpreter is
  `nockO ev (O_k) s t`; `interp_bad`: `k ≥ 13` crashes.
- The dynamic axis walks: `slotB` at axis `n` is Nock's `/` (`slotB_enc`,
  `slotB_none`), `editB` is `#` (`editB_enc`, through `editP_enc`, the
  twin of the compiled `editT_enc`).

Everything here is β (`Interp.lean`'s `_beta` lemmas) and the eliminators
of the Scott sum; the recursion of `nockI` itself is the simulation's
induction.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- Meeting an optional noun
-- ---------------------------------------------------------------------------

/-- The SKI term `e` meets the optional noun: an encoding of it, or `Err`. -/
def Meets : Option Noun → Term → Prop
  | some r, e => ∃ er, Enc r er ∧ WSteps e er
  | none, e => WSteps e errT

theorem Meets.back {o : Option Noun} {e e' : Term} (h : WSteps e e') (hm : Meets o e') : Meets o e := by
  cases o with
  | none => exact h.trans hm
  | some r =>
    obtain ⟨er, her, he⟩ := hm
    exact ⟨er, her, h.trans he⟩

theorem boolT_tt (X Y : Term) : WSteps (boolT true ⬝ X ⬝ Y) X := Compose.boolT_sel true X Y
theorem boolT_ff (X Y : Term) : WSteps (boolT false ⬝ X ⬝ Y) Y := Compose.boolT_sel false X Y

-- ---------------------------------------------------------------------------
-- The dispatch
-- ---------------------------------------------------------------------------

/-- One unfolding of `nockI` on its two arguments. -/
theorem nockI_step (s f : Term) :
    WSteps (nockIFix ⬝ s ⬝ f) (f ⬝ nockIK0 ⬝ (nockIK1 ⬝ nockIFix ⬝ s) ⬝ (nockIK2 ⬝ s) ⬝ ErrC) :=
  (WSteps.left _ (WSteps.left _ nockI_unfold)).trans (nockIG_beta _ _ _)

/-- **`nockI`** on an atom formula crashes. -/
theorem nockI_atom (s b : Term) : WSteps (nockIFix ⬝ s ⬝ atomT b) errT :=
  (nockI_step _ _).trans ((atomT_elim _ _ _ _ _).trans (nockIK0_beta _))

/-- **`nockI`** on a plain cell goes to `nockP` with the halves. -/
theorem nockI_cell (s eh et : Term) :
    WSteps (nockIFix ⬝ s ⬝ cellT eh et) (nockPT ⬝ nockIFix ⬝ s ⬝ eh ⬝ et) :=
  (nockI_step _ _).trans ((cellT_elim _ _ _ _ _ _).trans (nockIK1_beta _ _ _ _))

/-- **`nockI`** on a `Form` runs its code. -/
theorem nockI_form (s eh et c : Term) : WSteps (nockIFix ⬝ s ⬝ formT eh et c) (c ⬝ s) :=
  (nockI_step _ _).trans ((formT_elim _ _ _ _ _ _ _).trans (nockIK2_beta _ _ _ _))

theorem nockI_err (s : Term) : WSteps (nockIFix ⬝ s ⬝ errT) errT :=
  (nockI_step _ _).trans (errT_elim _ _ _ _)

/-- **`nockP`** with an atom head reads the opcode and dispatches. -/
theorem nockP_atom (ev s b t : Term) :
    WSteps (nockPT ⬝ ev ⬝ s ⬝ atomT b ⬝ t) (nockOT ⬝ ev ⬝ (decopT ⬝ b) ⬝ s ⬝ t) :=
  (nockPT_beta _ _ _ _).trans ((atomT_elim _ _ _ _ _).trans (nockPK0_beta _ _ _ _))

/-- **`nockP`** with a cell head is an autocons. -/
theorem nockP_cell (ev s eh et t : Term) :
    WSteps (nockPT ⬝ ev ⬝ s ⬝ cellT eh et ⬝ t) (autoconsT ⬝ ev ⬝ s ⬝ cellT eh et ⬝ t) :=
  (nockPT_beta _ _ _ _).trans ((cellT_elim _ _ _ _ _ _).trans (nockPK1_beta _ _ _ _ _ _))

theorem nockP_form (ev s eh et c t : Term) :
    WSteps (nockPT ⬝ ev ⬝ s ⬝ formT eh et c ⬝ t) (autoconsT ⬝ ev ⬝ s ⬝ formT eh et c ⬝ t) :=
  (nockPT_beta _ _ _ _).trans ((formT_elim _ _ _ _ _ _ _).trans (nockPK2_beta _ _ _ _ _ _ _))

/-- **`autocons`**: force the head's value, then the tail's, then `Cell`. -/
theorem autoconsK0_cell (x y : Term) : WSteps (autoconsK0 ⬝ x ⬝ y) (cellT x y) :=
  (autoconsK0_beta _ _).trans (CellC_red _ _)

/-- The interpreter on an autocons formula, whatever the head's encoding. -/
theorem interp_autocons {b c : Noun} {eh : Term} (hh : Enc (.cell b c) eh) (es et : Term) :
    WSteps (nockIFix ⬝ es ⬝ cellT eh et)
      (forceT ⬝ (nockIFix ⬝ es ⬝ eh) ⬝ (autoconsK1 ⬝ nockIFix ⬝ es ⬝ et)) := by
  refine (nockI_cell _ _ _).trans ?_
  cases hh with
  | cell _ _ => exact (nockP_cell _ _ _ _ _).trans (autoconsT_beta _ _ _ _)
  | form _ _ => exact (nockP_form _ _ _ _ _ _).trans (autoconsT_beta _ _ _ _)

/-- **`appI`**: `app` with the evaluator passed in. -/
theorem appI_atom (ev b x : Term) : WSteps (appIT ⬝ ev ⬝ atomT b ⬝ x) errT :=
  (appIT_beta _ _ _).trans ((atomT_elim _ _ _ _ _).trans (appIK0_beta _))

theorem appI_cell (ev eh et x : Term) : WSteps (appIT ⬝ ev ⬝ cellT eh et ⬝ x) (ev ⬝ x ⬝ cellT eh et) :=
  (appIT_beta _ _ _).trans ((cellT_elim _ _ _ _ _ _).trans (appIK1_beta _ _ _ _ _))

theorem appI_form (ev eh et c x : Term) : WSteps (appIT ⬝ ev ⬝ formT eh et c ⬝ x) (c ⬝ x) :=
  (appIT_beta _ _ _).trans ((formT_elim _ _ _ _ _ _ _).trans (appIK2_beta _ _ _ _))

theorem appI_err (ev x : Term) : WSteps (appIT ⬝ ev ⬝ errT ⬝ x) errT :=
  (appIT_beta _ _ _).trans (errT_elim _ _ _ _)

/-- **`cel2`** hands an encoded cell's halves to its continuation. -/
theorem cel2_enc {h t : Noun} {e : Term} (he : Enc (.cell h t) e) (k : Term) :
    ∃ eh et, Enc h eh ∧ Enc t et ∧ WSteps (cel2T ⬝ e ⬝ k) (k ⬝ eh ⬝ et) := by
  cases he with
  | cell hh ht =>
    exact ⟨_, _, hh, ht, (cel2T_beta _ _).trans ((cellT_elim _ _ _ _ _ _).trans (cel2K1_beta _ _ _))⟩
  | form hh ht =>
    exact ⟨_, _, hh, ht, (cel2T_beta _ _).trans ((formT_elim _ _ _ _ _ _ _).trans (cel2K2_beta _ _ _ _))⟩

/-- **`cel2`** crashes on an atom. -/
theorem cel2_atom {n : Nat} {e : Term} (he : Enc (.atom n) e) (k : Term) : WSteps (cel2T ⬝ e ⬝ k) errT := by
  rw [he.atom_inv]
  exact (cel2T_beta _ _).trans ((atomT_elim _ _ _ _ _).trans (cel2K0_beta _))

-- ---------------------------------------------------------------------------
-- Opcodes: the plain cell `[k t]`
-- ---------------------------------------------------------------------------

/-- The interpreter on a plain cell `[k t]`, `k ≤ 12`: the opcode's bits
    are read and `nockO` runs on the tag. -/
theorem interp_op {k : Nat} (hk : k ≤ 12) (es et : Term) :
    WSteps (nockIFix ⬝ es ⬝ cellT (encNoun (.atom k)) et) (nockOT ⬝ nockIFix ⬝ opC k ⬝ es ⬝ et) :=
  (nockI_cell _ _ _).trans ((nockP_atom _ _ _ _).trans
    (WSteps.left _ (WSteps.left _ (WSteps.right _ (decop_le hk)))))

/-- An opcode from 13 on is a crash. -/
theorem interp_bad {k : Nat} (hk : 13 ≤ k) (es et : Term) :
    WSteps (nockIFix ⬝ es ⬝ cellT (encNoun (.atom k)) et) errT :=
  (nockI_cell _ _ _).trans ((nockP_atom _ _ _ _).trans
    ((WSteps.left _ (WSteps.left _ (WSteps.right _ (decop_bad hk)))).trans (nockO_Obad _ _ _)))

-- ---------------------------------------------------------------------------
-- slotB: Nock's `/` at a dynamic axis
-- ---------------------------------------------------------------------------

/-- **`slotB`** at axis `n` of an encoding is an encoding of `/[n x]`. -/
theorem slotB_enc {n : Nat} {x y : Noun} {ex : Term} (hf : fasO (.atom n) x = some y) (hx : Enc x ex) :
    ∃ ey, Enc y ey ∧ WSteps (slotBT ⬝ bitsT (bits n) ⬝ ex) ey := by
  cases n with
  | zero => rw [fasO_zero] at hf; cases hf
  | succ k =>
    rw [fasO_axisPath _ _ (by omega)] at hf
    obtain ⟨ey, hy, hp⟩ := pick_enc _ y hf hx (.refl ex)
    exact ⟨ey, hy, (slotB_pos (k + 1) (by omega) ex).trans hp⟩

/-- **`slotB`** crashes where `/` does. -/
theorem slotB_none {n : Nat} {x : Noun} {ex : Term} (hf : fasO (.atom n) x = none) (hx : Enc x ex) :
    WSteps (slotBT ⬝ bitsT (bits n) ⬝ ex) errT := by
  cases n with
  | zero => exact slotB_zero ex
  | succ k =>
    rw [fasO_axisPath _ _ (by omega)] at hf
    exact (slotB_pos (k + 1) (by omega) ex).trans (pick_enc_none _ hf hx (.refl ex))

-- ---------------------------------------------------------------------------
-- editP, editB: Nock's `#` at a dynamic axis
-- ---------------------------------------------------------------------------

/-- **`editP`** meets `editP`: the path rebuilt with forced projections,
    a crash into an atom (the twin of `editT_enc`). -/
theorem editP_enc : ∀ (bs : List Bool) {v t : Noun} {ev et : Term}, Enc v ev → Enc t et →
    Meets (editP v bs t) (editPFix ⬝ bitsT bs ⬝ ev ⬝ et)
  | [], v, t, ev, et, hv, _ =>
    ⟨ev, hv, (WSteps.left _ (WSteps.left _ (WSteps.left _ editP_unfold))).trans
      ((editPG_beta _ _ _ _).trans (nilT_elim _ _))⟩
  | b :: bs, v, t, ev, et, hv, ht => by
    have h1 : WSteps (editPFix ⬝ bitsT (b :: bs) ⬝ ev ⬝ et)
        (forceT ⬝ (hdT ⬝ et) ⬝ (editPK3 ⬝ editPFix ⬝ ev ⬝ et ⬝ boolT b ⬝ bitsT bs)) :=
      (WSteps.left _ (WSteps.left _ (WSteps.left _ editP_unfold))).trans ((editPG_beta _ _ _ _).trans
        ((consT_elim _ _ _ _).trans (editPK4_beta _ _ _ _ _)))
    refine Meets.back h1 ?_
    cases t with
    | atom n =>
      rw [editP_atom]
      exact (WSteps.left _ (WSteps.right _ (hd_enc_atom ht))).trans (force_err _)
    | cell l r =>
      obtain ⟨el, hl, hhd⟩ := hd_enc ht
      obtain ⟨er, hr, htl⟩ := tl_enc ht
      have h2 : WSteps (forceT ⬝ (hdT ⬝ et) ⬝ (editPK3 ⬝ editPFix ⬝ ev ⬝ et ⬝ boolT b ⬝ bitsT bs))
          (boolT b ⬝ (forceT ⬝ (editPFix ⬝ bitsT bs ⬝ ev ⬝ er) ⬝ (editPK0 ⬝ el))
            ⬝ (forceT ⬝ (editPFix ⬝ bitsT bs ⬝ ev ⬝ el) ⬝ (editPK1 ⬝ er))) :=
        (WSteps.left _ (WSteps.right _ hhd)).trans ((force_enc hl _).trans ((editPK3_beta _ _ _ _ _ _).trans
          ((WSteps.left _ (WSteps.right _ htl)).trans ((force_enc hr _).trans (editPK2_beta _ _ _ _ _ _)))))
      refine Meets.back h2 ?_
      cases b with
      | true =>
        refine Meets.back (boolT_tt _ _) ?_
        show Meets ((editP v bs r).map (fun r' => Noun.cell l r')) _
        have ih := editP_enc bs hv hr
        cases hE : editP v bs r with
        | none =>
          rw [hE] at ih
          exact (WSteps.left _ (WSteps.right _ ih)).trans (force_err _)
        | some r' =>
          rw [hE] at ih
          obtain ⟨ei, hi, hei⟩ := ih
          exact ⟨cellT el ei, .cell hl hi, (WSteps.left _ (WSteps.right _ hei)).trans
            ((force_enc hi _).trans ((editPK0_beta _ _).trans (CellC_red _ _)))⟩
      | false =>
        refine Meets.back (boolT_ff _ _) ?_
        show Meets ((editP v bs l).map (fun l' => Noun.cell l' r)) _
        have ih := editP_enc bs hv hl
        cases hE : editP v bs l with
        | none =>
          rw [hE] at ih
          exact (WSteps.left _ (WSteps.right _ ih)).trans (force_err _)
        | some l' =>
          rw [hE] at ih
          obtain ⟨ei, hi, hei⟩ := ih
          exact ⟨cellT ei er, .cell hi hr, (WSteps.left _ (WSteps.right _ hei)).trans
            ((force_enc hi _).trans ((editPK1_beta _ _).trans (CellC_red _ _)))⟩

/-- **`editB`** at axis `n` meets `#[n v t]`. -/
theorem editB_enc {n : Nat} {v t : Noun} {ev et : Term} (hv : Enc v ev) (ht : Enc t et) :
    Meets (haxO (.atom n) v t) (editBT ⬝ bitsT (bits n) ⬝ ev ⬝ et) := by
  cases n with
  | zero =>
    rw [haxO_zero, bits_zero]
    exact (editBT_beta _ _ _).trans (nilT_elim _ _)
  | succ k =>
    rw [haxO_axisPath _ _ _ (by omega)]
    have hb := bits_pos (n := k + 1) (by omega)
    have e1 : WSteps (ConsC ⬝ boolT ((k + 1) % 2 == 1) ⬝ bitsT (bits ((k + 1) / 2))) (bitsT (bits (k + 1))) := by
      rw [hb]; exact ConsC_red _ _
    rw [hb]
    refine Meets.back ((editBT_beta _ _ _).trans ((consT_elim _ _ _ _).trans
      ((editBK0_beta _ _ _ _).trans ?_))) (editP_enc _ hv ht)
    exact WSteps.left _ (WSteps.left _ ((WSteps.left _ editPT_fix).trans
      (WSteps.right _ ((WSteps.right _ e1).trans (path_spec (k + 1) (by omega))))))

end Nock2Ski
