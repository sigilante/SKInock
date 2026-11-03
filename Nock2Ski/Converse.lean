import Nock2Ski.Head
import Nock2Ski.Pending
import Nock2Ski.PredSkel

open Term

/-!
# The converse simulation: a SKI value is a Nock outcome (M4e)

`embed_value` and `embed_crash` (`Nock2Ski/Embed.lean`) carry a `NockEval`
derivation to the compiled term.  This module proves the converse,
`embed_terminates`: if `nockToSki f ⬝ es` reaches a weak head normal form
on an encoding `es` of `s`, then `NockEval s f o` for some `o`.  With the
forward simulation and `Eval.deterministic` that makes the three-valued
contract exact (`embed_outcome`, `embed_diverges`), and it closes the gap
README's hidden-subject statements left open: an accepted proof of
`nockPredV f k` shows an atom `n < 2^k` with `*[n f] = p` as a Nock
claim (`nock_pred_sound_nock`), and likewise for a skeleton
(`nock_predS_sound_nock`, `nock_pred2_sound_nock`).

## The argument

By contraposition through a measure on each side.  On the Nock side,
`Pending n s f` (`Nock2Ski/Pending.lean`) is a derivation cut off after
`n` costed steps, and `pending_of_noOut` says a run with no outcome is
pending at every `n`.  On the SKI side, `HLen t N` (`Nock2Ski/Head.lean`)
is "`t` reaches a weak head normal form in exactly `N` head
contractions".  `pending_both` is the simulation of a pending run: `n`
pending steps force at least `n` head contractions of the compiled term,
`Pending n s f → Enc s es → HLen (nockToSki f ⬝ es) N → n ≤ N`, and the
same of the interpreter `nockI` on any encoding of the formula, since
opcode 2 and 9 on a code-free cell run it (the two halves are one
induction, as `embed_both`).  Each case follows `embed_both`'s weak
reduction to the point where the pending operand sits under `force`
(`cel`, `inc`, `ifn`), where `hlen_force_pend` makes the operand's head
length strictly smaller; when the pending operand comes after values,
`embed_both` supplies the values' encodings and `hlen_force_enc` the
strict step.  The static hint costs nothing on either side.  So if the
compiled term normalizes in `N` steps, Nock cannot be pending at `N + 1`,
hence has an outcome.

Nothing of `Nock.Fuel` is needed: `Pending` is stated over `NockEval`
alone, so the root-name clash (`Diverges`, `Outcome`) does not arise,
and the statements use lean-ski's `Diverges` directly.
-/

namespace Nock2Ski

/-- `t`'s head length is at least `n`. -/
abbrev Bound (n : Nat) (t : Term) : Prop := ∀ {N : Nat}, HLen t N → n ≤ N

/-- The two halves at one node: the compiled term on an encoding of the
    subject, and the interpreter on an encoding of the formula. -/
def PendBoth (n : Nat) (s f : Noun) : Prop :=
  ∀ {es : Term}, Enc s es →
    Bound n (nockToSki f ⬝ es) ∧ ∀ {ef : Term}, Enc f ef → Bound n (nockIFix ⬝ es ⬝ ef)

theorem bound_zero (t : Term) : Bound 0 t := fun _ => Nat.zero_le _

/-- Both halves at a cell formula: the interpreter on a `Form` runs the
    compiled half. -/
theorem bound_cell {fh ft : Noun} {es : Term} {n : Nat} (hA : Bound n (nockToSki (.cell fh ft) ⬝ es))
    (hB : ∀ {eh et : Term}, Enc fh eh → Enc ft et → Bound n (nockIFix ⬝ es ⬝ cellT eh et)) :
    Bound n (nockToSki (.cell fh ft) ⬝ es) ∧
      ∀ {ef : Term}, Enc (.cell fh ft) ef → Bound n (nockIFix ⬝ es ⬝ ef) := by
  refine ⟨hA, fun hef => ?_⟩
  cases hef with
  | cell hh ht => exact hB hh ht
  | form hh ht => exact le_of_wsteps (nockI_form _ _ _ _) hA

/-- The interpreter's side of an opcode `k ≤ 12`. -/
theorem bound_at {k : Nat} (hk : k ≤ 12) {eh et : Term} (hh : Enc (.atom k) eh) {n : Nat} {es : Term}
    (h : Bound n (nockOT ⬝ nockIFix ⬝ opC k ⬝ es ⬝ et)) : Bound n (nockIFix ⬝ es ⬝ cellT eh et) := by
  rw [hh.atom_inv]
  exact le_of_wsteps (interp_op hk es et) h

/-- `app` of an encoded formula on an encoded subject: a `Form` runs its
    code, a `Cell` the interpreter, an atom is pending only at `0`. -/
theorem app_bound {r2 r1 : Noun} {e2 e1 : Term} {n : Nat} (hp : Pending n r1 r2)
    (ih : PendBoth n r1 r2) (h2 : Enc r2 e2) (h1 : Enc r1 e1) : Bound n (appT ⬝ e2 ⬝ e1) := by
  cases r2 with
  | atom m => rw [pending_atom hp]; exact bound_zero _
  | cell h t =>
    cases h2 with
    | cell hh ht =>
      exact le_of_wsteps ((app_cell _ _ _).trans (WSteps.left _ (WSteps.left _ nockIT_fix)))
        ((ih h1).2 (.cell hh ht))
    | form hh ht => exact le_of_wsteps (app_form _ _ _ _) (ih h1).1

theorem appI_bound {r2 r1 : Noun} {e2 e1 : Term} {n : Nat} (hp : Pending n r1 r2)
    (ih : PendBoth n r1 r2) (h2 : Enc r2 e2) (h1 : Enc r1 e1) :
    Bound n (appIT ⬝ nockIFix ⬝ e2 ⬝ e1) := by
  cases r2 with
  | atom m => rw [pending_atom hp]; exact bound_zero _
  | cell h t =>
    cases h2 with
    | cell hh ht => exact le_of_wsteps (appI_cell _ _ _ _) ((ih h1).2 (.cell hh ht))
    | form hh ht => exact le_of_wsteps (appI_form _ _ _ _ _) (ih h1).1

-- ---------------------------------------------------------------------------
-- The simulation of a pending run
-- ---------------------------------------------------------------------------

/-- **`n` pending Nock steps force at least `n` head contractions**, of the
    compiled term on any encoding of the subject and of the interpreter on
    any encodings of the subject and the formula. -/
theorem pending_both {n : Nat} {s f : Noun} (h : Pending n s f) : PendBoth n s f := by
  induction h with
  | zero => intro es _; exact ⟨bound_zero _, fun _ => bound_zero _⟩
  -- autocons
  | @autocons_L n a b c d _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_force_pend (step_autocons b c d es) (ih hes).1
    · exact le_force_pend (interp_autocons hh es _) ((ih hes).2 hh)
  | @autocons_R n a b c d r1 hb _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).1
      exact le_force_pend ((step_autocons b c d es).trans ((WSteps.left _ (WSteps.right _ hB)).trans
        ((force_enc he1 _).trans (consK_beta _ _)))) (ih hes).1
    · obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).2 hh
      exact le_force_pend ((interp_autocons hh es _).trans ((WSteps.left _ (WSteps.right _ hB)).trans
        ((force_enc he1 _).trans (autoconsK1_beta _ _ _ _)))) ((ih hes).2 ht)
  -- 2
  | @op2_b n a b c _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_force_pend (step_op2 b c es) (ih hes).1
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK5 ⬝ nockIFix ⬝ es)
      exact bound_at (by decide) hh
        (le_force_pend ((nockO_O2 _ _ _).trans (h1.trans (nockOK5_beta _ _ _ _))) ((ih hes).2 hb))
  | @op2_c n a b c r1 hb _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).1
      obtain ⟨kx, hk, _⟩ := appK_beta (nockToSki c ⬝ es) e1
      exact le_force_pend ((step_op2 b c es).trans ((WSteps.left _ (WSteps.right _ hB)).trans
        ((force_enc he1 _).trans hk))) (ih hes).1
    · obtain ⟨eb, ec, hb', hc, h1⟩ := cel2_enc ht (nockOK5 ⬝ nockIFix ⬝ es)
      obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).2 hb'
      exact bound_at (by decide) hh (le_force_pend ((nockO_O2 _ _ _).trans (h1.trans
        ((nockOK5_beta _ _ _ _).trans ((WSteps.left _ (WSteps.right _ hB)).trans
        ((force_enc he1 _).trans (nockOK4_beta _ _ _ _)))))) ((ih hes).2 hc))
  | @op2_run n a b c r1 r2 hb hc hp ih3 =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).1
      obtain ⟨e2, he2, hC⟩ := (embed_both hc hes).1
      obtain ⟨kx, hk, hkx⟩ := appK_beta (nockToSki c ⬝ es) e1
      exact le_force_enc ((step_op2 b c es).trans ((WSteps.left _ (WSteps.right _ hB)).trans
        ((force_enc he1 _).trans (hk.trans (WSteps.left _ (WSteps.right _ hC)))))) he2 (hkx e2)
        (app_bound hp ih3 he2 he1)
    · obtain ⟨eb, ec, hb', hc', h1⟩ := cel2_enc ht (nockOK5 ⬝ nockIFix ⬝ es)
      obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).2 hb'
      obtain ⟨e2, he2, hC⟩ := (embed_both hc hes).2 hc'
      exact bound_at (by decide) hh (le_force_enc ((nockO_O2 _ _ _).trans (h1.trans
        ((nockOK5_beta _ _ _ _).trans ((WSteps.left _ (WSteps.right _ hB)).trans ((force_enc he1 _).trans
        ((nockOK4_beta _ _ _ _).trans (WSteps.left _ (WSteps.right _ hC)))))))) he2 (nockOK3_beta _ _ _)
        (appI_bound hp ih3 he2 he1))
  -- 3, 4
  | @op3 n a b _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_cel_pend (step_op3 b es) (ih hes).1
    · exact bound_at (by decide) hh (le_cel_pend (nockO_O3 _ _ _) ((ih hes).2 ht))
  | @op4 n a b _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_inc_pend (step_op4 b es) (ih hes).1
    · exact bound_at (by decide) hh (le_inc_pend (nockO_O4 _ _ _) ((ih hes).2 ht))
  -- 5
  | @op5_b n a b c _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_force_pend (step_op5 b c es) (ih hes).1
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK8 ⬝ nockIFix ⬝ es)
      exact bound_at (by decide) hh
        (le_force_pend ((nockO_O5 _ _ _).trans (h1.trans (nockOK8_beta _ _ _ _))) ((ih hes).2 hb))
  | @op5_c n a b c r1 hb _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).1
      exact le_force_pend ((step_op5 b c es).trans ((WSteps.left _ (WSteps.right _ hB)).trans
        ((force_enc he1 _).trans (eqK_beta _ _)))) (ih hes).1
    · obtain ⟨eb, ec, hb', hc, h1⟩ := cel2_enc ht (nockOK8 ⬝ nockIFix ⬝ es)
      obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).2 hb'
      exact bound_at (by decide) hh (le_force_pend ((nockO_O5 _ _ _).trans (h1.trans
        ((nockOK8_beta _ _ _ _).trans ((WSteps.left _ (WSteps.right _ hB)).trans
        ((force_enc he1 _).trans (nockOK7_beta _ _ _ _)))))) ((ih hes).2 hc))
  -- 6
  | @op6_b n a b c d _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_ifn_pend (step_op6 b c d es) (ih hes).1
    · obtain ⟨eb, ecd, hb, hcd, h1⟩ := cel2_enc ht (nockOK10 ⬝ nockIFix ⬝ es)
      obtain ⟨ec, ed, hc, hd, h2⟩ := cel2_enc hcd (nockOK9 ⬝ nockIFix ⬝ es ⬝ eb)
      exact bound_at (by decide) hh (le_ifn_pend ((nockO_O6 _ _ _).trans (h1.trans
        ((nockOK10_beta _ _ _ _).trans (h2.trans (nockOK9_beta _ _ _ _ _))))) ((ih hes).2 hb))
  | @op6_then n a b c d hb _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e, he, hB⟩ := (embed_both hb hes).1
      rw [he.atom_inv] at hB
      exact le_ifn_zero ((step_op6 b c d es).trans (WSteps.left _ (WSteps.left _ (WSteps.right _ hB))))
        (ih hes).1
    · obtain ⟨eb, ecd, hb', hcd, h1⟩ := cel2_enc ht (nockOK10 ⬝ nockIFix ⬝ es)
      obtain ⟨ec, ed, hc, hd, h2⟩ := cel2_enc hcd (nockOK9 ⬝ nockIFix ⬝ es ⬝ eb)
      obtain ⟨e, he, hB⟩ := (embed_both hb hes).2 hb'
      rw [he.atom_inv] at hB
      exact bound_at (by decide) hh (le_ifn_zero ((nockO_O6 _ _ _).trans (h1.trans
        ((nockOK10_beta _ _ _ _).trans (h2.trans ((nockOK9_beta _ _ _ _ _).trans
        (WSteps.left _ (WSteps.left _ (WSteps.right _ hB)))))))) ((ih hes).2 hc))
  | @op6_else n a b c d hb _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e, he, hB⟩ := (embed_both hb hes).1
      rw [he.atom_inv] at hB
      exact le_ifn_one ((step_op6 b c d es).trans (WSteps.left _ (WSteps.left _ (WSteps.right _ hB))))
        (ih hes).1
    · obtain ⟨eb, ecd, hb', hcd, h1⟩ := cel2_enc ht (nockOK10 ⬝ nockIFix ⬝ es)
      obtain ⟨ec, ed, hc, hd, h2⟩ := cel2_enc hcd (nockOK9 ⬝ nockIFix ⬝ es ⬝ eb)
      obtain ⟨e, he, hB⟩ := (embed_both hb hes).2 hb'
      rw [he.atom_inv] at hB
      exact bound_at (by decide) hh (le_ifn_one ((nockO_O6 _ _ _).trans (h1.trans
        ((nockOK10_beta _ _ _ _).trans (h2.trans ((nockOK9_beta _ _ _ _ _).trans
        (WSteps.left _ (WSteps.left _ (WSteps.right _ hB)))))))) ((ih hes).2 hd))
  -- 7
  | @op7_b n a b c _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_force_pend (step_op7 b c es) (ih hes).1
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK12 ⬝ nockIFix ⬝ es)
      exact bound_at (by decide) hh
        (le_force_pend ((nockO_O7 _ _ _).trans (h1.trans (nockOK12_beta _ _ _ _))) ((ih hes).2 hb))
  | @op7_c n a b c r1 hb _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).1
      exact le_force_enc ((step_op7 b c es).trans (WSteps.left _ (WSteps.right _ hB))) he1 (.refl _)
        (ih he1).1
    · obtain ⟨eb, ec, hb', hc, h1⟩ := cel2_enc ht (nockOK12 ⬝ nockIFix ⬝ es)
      obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).2 hb'
      exact bound_at (by decide) hh (le_force_enc ((nockO_O7 _ _ _).trans (h1.trans
        ((nockOK12_beta _ _ _ _).trans (WSteps.left _ (WSteps.right _ hB))))) he1 (nockOK11_beta _ _ _)
        ((ih he1).2 hc))
  -- 8
  | @op8_b n a b c _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_force_pend (step_op8 b c es) (ih hes).1
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK14 ⬝ nockIFix ⬝ es)
      exact bound_at (by decide) hh
        (le_force_pend ((nockO_O8 _ _ _).trans (h1.trans (nockOK14_beta _ _ _ _))) ((ih hes).2 hb))
  | @op8_c n a b c r1 hb _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).1
      exact le_force_enc ((step_op8 b c es).trans (WSteps.left _ (WSteps.right _ hB))) he1
        ((pushK_beta _ _ _).trans (WSteps.right _ (CellC_red e1 es))) (ih (.cell he1 hes)).1
    · obtain ⟨eb, ec, hb', hc, h1⟩ := cel2_enc ht (nockOK14 ⬝ nockIFix ⬝ es)
      obtain ⟨e1, he1, hB⟩ := (embed_both hb hes).2 hb'
      exact bound_at (by decide) hh (le_force_enc ((nockO_O8 _ _ _).trans (h1.trans
        ((nockOK14_beta _ _ _ _).trans (WSteps.left _ (WSteps.right _ hB))))) he1
        ((nockOK13_beta _ _ _ _).trans (WSteps.left _ (WSteps.right _ (CellC_red e1 es))))
        ((ih (.cell he1 hes)).2 hc))
  -- 9
  | @op9_c n a b c _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_force_pend (step_op9 b c es) (ih hes).1
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK19 ⬝ nockIFix ⬝ es)
      exact bound_at (by decide) hh
        (le_force_pend ((nockO_O9 _ _ _).trans (h1.trans (nockOK19_beta _ _ _ _))) ((ih hes).2 hc))
  | @op9_arm n a b c core arm hc hfas hp ih3 =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨ec, hec, hC⟩ := (embed_both hc hes).1
      cases b with
      | cell p q => rw [fasO_cell] at hfas; cases hfas
      | atom m =>
        cases m with
        | zero => rw [fasO_zero] at hfas; cases hfas
        | succ k =>
          rw [fasO_axisPath _ _ (by omega)] at hfas
          obtain ⟨ea, hea, hp'⟩ := pick_enc _ arm hfas hec (.refl ec)
          exact le_force_enc ((step_op9 _ c es).trans (WSteps.left _ (WSteps.right _ hC))) hec
            ((pullK_succ k ec).trans (WSteps.left _ (WSteps.right _ hp'))) (app_bound hp ih3 hea hec)
    · obtain ⟨eb, ec', hb, hc', h1⟩ := cel2_enc ht (nockOK19 ⬝ nockIFix ⬝ es)
      obtain ⟨ecore, hcore, hC⟩ := (embed_both hc hes).2 hc'
      cases b with
      | cell p q => rw [fasO_cell] at hfas; cases hfas
      | atom m =>
        rw [hb.atom_inv] at h1
        obtain ⟨ea, hea, hsl⟩ := slotB_enc hfas hcore
        exact bound_at (by decide) hh (le_force_enc ((nockO_O9 _ _ _).trans (h1.trans
          ((nockOK19_beta _ _ _ _).trans (WSteps.left _ (WSteps.right _ hC))))) hcore
          ((nockOK18_beta _ _ _).trans ((atomT_elim _ _ _ _ _).trans ((nockOK15_beta _ _ _).trans
          (WSteps.left _ (WSteps.right _ hsl))))) (appI_bound hp ih3 hea hcore))
  -- 10
  | @op10_d n a b c d _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_force_pend (step_op10 b c d es) (ih hes).1
    · obtain ⟨ebc, ed, hbc, hd, h1⟩ := cel2_enc ht (nockOK26 ⬝ nockIFix ⬝ es)
      obtain ⟨eb, ec, hb, hc, h2⟩ := cel2_enc hbc (nockOK25 ⬝ nockIFix ⬝ es ⬝ ed)
      exact bound_at (by decide) hh (le_force_pend ((nockO_O10 _ _ _).trans (h1.trans
        ((nockOK26_beta _ _ _ _).trans (h2.trans (nockOK25_beta _ _ _ _ _))))) ((ih hes).2 hd))
  | @op10_c n a b c d r2 hd _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e2, he2, hD⟩ := (embed_both hd hes).1
      obtain ⟨kv, hk, _⟩ := editK_beta b (nockToSki c ⬝ es) e2
      exact le_force_pend ((step_op10 b c d es).trans ((WSteps.left _ (WSteps.right _ hD)).trans
        ((force_enc he2 _).trans hk))) (ih hes).1
    · obtain ⟨ebc, ed, hbc, hd', h1⟩ := cel2_enc ht (nockOK26 ⬝ nockIFix ⬝ es)
      obtain ⟨eb, ec, hb, hc, h2⟩ := cel2_enc hbc (nockOK25 ⬝ nockIFix ⬝ es ⬝ ed)
      obtain ⟨e2, he2, hD⟩ := (embed_both hd hes).2 hd'
      exact bound_at (by decide) hh (le_force_pend ((nockO_O10 _ _ _).trans (h1.trans
        ((nockOK26_beta _ _ _ _).trans (h2.trans ((nockOK25_beta _ _ _ _ _).trans
        ((WSteps.left _ (WSteps.right _ hD)).trans ((force_enc he2 _).trans
        (nockOK24_beta _ _ _ _ _)))))))) ((ih hes).2 hc))
  -- 11
  | @op11_static n a t c _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · rw [step_op11_static]; exact (ih hes).1
    · obtain ⟨eh, ec, hh', hc, h1⟩ := cel2_enc ht (nockOK32 ⬝ nockIFix ⬝ es)
      rw [hh'.atom_inv] at h1
      exact bound_at (by decide) hh (le_of_wsteps ((nockO_O11 _ _ _).trans (h1.trans
        ((nockOK32_beta _ _ _ _).trans ((atomT_elim _ _ _ _ _).trans (nockOK27_beta _ _ _ _)))))
        ((ih hes).2 hc))
  | @op11_dyn_c n a t c d _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · exact le_force_pend (step_op11_dynamic t c d es) (ih hes).1
    · obtain ⟨etc, ed, htc, hd, h1⟩ := cel2_enc ht (nockOK32 ⬝ nockIFix ⬝ es)
      refine bound_at (by decide) hh ?_
      cases htc with
      | @cell _ _ et' ec _ hc =>
        exact le_force_pend ((nockO_O11 _ _ _).trans (h1.trans ((nockOK32_beta _ _ _ _).trans
          ((cellT_elim _ _ _ _ _ _).trans (nockOK29_beta _ _ _ _ _))))) ((ih hes).2 hc)
      | @form _ _ et' ec _ hc =>
        exact le_force_pend ((nockO_O11 _ _ _).trans (h1.trans ((nockOK32_beta _ _ _ _).trans
          ((formT_elim _ _ _ _ _ _ _).trans (nockOK31_beta _ _ _ _ _ _))))) ((ih hes).2 hc)
  | @op11_dyn_d n a t c d r1 hc _ ih =>
    intro es hes
    refine bound_cell ?_ fun hh ht => ?_
    · obtain ⟨e1, he1, hC⟩ := (embed_both hc hes).1
      exact le_force_enc ((step_op11_dynamic t c d es).trans (WSteps.left _ (WSteps.right _ hC))) he1
        (.single (.K _ _)) (ih hes).1
    · obtain ⟨etc, ed, htc, hd, h1⟩ := cel2_enc ht (nockOK32 ⬝ nockIFix ⬝ es)
      refine bound_at (by decide) hh ?_
      cases htc with
      | @cell _ _ et' ec _ hc' =>
        obtain ⟨e1, he1, hC⟩ := (embed_both hc hes).2 hc'
        exact le_force_enc ((nockO_O11 _ _ _).trans (h1.trans ((nockOK32_beta _ _ _ _).trans
          ((cellT_elim _ _ _ _ _ _).trans ((nockOK29_beta _ _ _ _ _).trans
          (WSteps.left _ (WSteps.right _ hC))))))) he1 (nockOK28_beta _ _ _ _) ((ih hes).2 hd)
      | @form _ _ et' ec _ hc' =>
        obtain ⟨e1, he1, hC⟩ := (embed_both hc hes).2 hc'
        exact le_force_enc ((nockO_O11 _ _ _).trans (h1.trans ((nockOK32_beta _ _ _ _).trans
          ((formT_elim _ _ _ _ _ _ _).trans ((nockOK31_beta _ _ _ _ _ _).trans
          (WSteps.left _ (WSteps.right _ hC))))))) he1 (nockOK30_beta _ _ _ _) ((ih hes).2 hd)

-- ---------------------------------------------------------------------------
-- The converse
-- ---------------------------------------------------------------------------

/-- **`embed_terminates`**: if the compiled term reaches a weak head normal
    form on an encoding of the subject, Nock has an outcome. -/
theorem embed_terminates {s f : Noun} {es v : Term} (hes : Enc s es)
    (h : Eval (nockToSki f ⬝ es) v) : ∃ o, NockEval s f o := by
  refine Classical.byContradiction fun hno => ?_
  have hn : NoOut s f := fun o ho => hno ⟨o, ho⟩
  obtain ⟨N, hN⟩ := hlen_of_eval h
  have := (pending_both (pending_of_noOut (N + 1) f s hn) hes).1 hN
  omega

/-- The same of the interpreter on encodings of the subject and the formula. -/
theorem nockI_terminates {s f : Noun} {es ef v : Term} (hes : Enc s es) (hef : Enc f ef)
    (h : Eval (nockIT ⬝ es ⬝ ef) v) : ∃ o, NockEval s f o := by
  refine Classical.byContradiction fun hno => ?_
  have hn : NoOut s f := fun o ho => hno ⟨o, ho⟩
  obtain ⟨N, hN⟩ := hlen_of_eval h
  obtain ⟨M, hM, hN'⟩ := hlen_wsteps (WSteps.left _ (WSteps.left _ nockIT_fix)) hN
  have := (pending_both (pending_of_noOut (N + 1) f s hn) hes).2 hef hN'
  omega

/-- **`embed_outcome`**: the weak head normal form of the compiled term is an
    encoding of Nock's value, or `Err` where Nock crashes, and Nock does
    one or the other. -/
theorem embed_outcome {s f : Noun} {es v : Term} (hes : Enc s es) (h : Eval (nockToSki f ⬝ es) v) :
    (∃ p ep, NockEval s f (.val p) ∧ Enc p ep ∧ WSteps v ep) ∨
      (NockEval s f .exit ∧ WSteps v errT) := by
  obtain ⟨o, ho⟩ := embed_terminates hes h
  cases o with
  | val p =>
    obtain ⟨ep, hp, he⟩ := embed_value ho hes
    exact .inl ⟨p, ep, ho, hp, eval_enc hp he h⟩
  | exit => exact .inr ⟨ho, eval_wsteps whnf_errT (embed_crash ho hes) h⟩

/-- **`embed_complete`**: a weak head normal form that is not `Err` is an
    encoding of Nock's value. -/
theorem embed_complete {s f : Noun} {es v : Term} (hes : Enc s es) (h : Eval (nockToSki f ⬝ es) v)
    (hv : ¬ WSteps v errT) : ∃ p ep, NockEval s f (.val p) ∧ Enc p ep ∧ WSteps v ep := by
  rcases embed_outcome hes h with hval | ⟨_, herr⟩
  · exact hval
  · exact absurd herr hv

/-- **`embed_diverges`** (PLAN.md §2.4): the compiled term diverges exactly
    when Nock derives no outcome.  `Diverges` is lean-ski's. -/
theorem embed_diverges {s f : Noun} {es : Term} (hes : Enc s es) :
    Diverges (nockToSki f ⬝ es) ↔ ∀ o, ¬ NockEval s f o := by
  constructor
  · intro hd o ho
    cases o with
    | val p =>
      obtain ⟨ep, hp, he⟩ := embed_value ho hes
      obtain ⟨v, hv, _⟩ := eval_back he ⟨.refl ep, enc_whnf hp⟩
      exact hd v hv
    | exit =>
      obtain ⟨v, hv, _⟩ := eval_back (embed_crash ho hes) ⟨.refl errT, whnf_errT⟩
      exact hd v hv
  · intro hno v hv
    obtain ⟨o, ho⟩ := embed_terminates hes hv
    exact hno o ho

/-- On the released rows: `compiled f s` and `share (compiled f s)`. -/
theorem compiled_terminates {s f : Noun} {v : Term} (h : Eval (compiled f s) v) :
    ∃ o, NockEval s f o :=
  embed_terminates (enc_encLit s) h

theorem shared_terminates {s f : Noun} {v : Term} (h : Eval (share (compiled f s)) v) :
    ∃ o, NockEval s f o := by
  obtain ⟨N, hN⟩ := hlen_of_eval h
  obtain ⟨M, _, hM⟩ := hlen_wsteps (share_red _) hN
  obtain ⟨v', hv'⟩ := hM.eval
  exact compiled_terminates hv'

-- ---------------------------------------------------------------------------
-- The hidden-subject statements as Nock claims
-- ---------------------------------------------------------------------------

/-- **The SKI-level verdict is a Nock claim**: if `eqn` accepts the compiled
    formula's result on `encNoun s` against `encNoun p`, Nock evaluates `f`
    on `s` to `p`.  `eqn` forces its first argument (`hlen_eqn_pend`), so
    the compiled term reaches a weak head normal form and Nock has an
    outcome (`embed_terminates`); it is not a crash
    (`nock_pred_sound_crash`) and its value is `p` (`nock_pred_sound_val`). -/
theorem nock_of_eqn_K {f p s : Noun}
    (hK : WSteps (eqnFix ⬝ (nockToSki f ⬝ encNoun s) ⬝ encNoun p) K) : NockEval s f (.val p) := by
  obtain ⟨v, hv, _⟩ := eval_back hK ⟨.refl K, .K⟩
  obtain ⟨N, hN⟩ := hlen_of_eval hv
  obtain ⟨M, _, hM⟩ := hlen_eqn_pend hN
  obtain ⟨u, hu⟩ := hM.eval
  obtain ⟨o, ho⟩ := embed_terminates (enc_encNoun s) hu
  cases o with
  | exit => exact absurd ho (nock_pred_sound_crash hK)
  | val q => exact (nock_pred_sound_val hK ho) ▸ ho

/-- **`nock_pred_sound_nock`** (M4c's statement closed): the verifier
    accepting `encNoun p` on `k` bits shows an atom `n < 2^k` with
    `*[n f] = p`, as a `NockEval` derivation. -/
theorem nock_pred_sound_nock {f p : Noun} {k : Nat} {bs : List Bool} (hk : 0 < k)
    (hl : bs.length = k) (h : Eval (nockPredV f k ⬝ encNoun p ⬝ boolsT bs) K) :
    ∃ n, n < 2 ^ k ∧ NockEval (.atom n) f (.val p) :=
  let ⟨n, hn, hK, _, _⟩ := nock_pred_sound hk hl h
  ⟨n, hn, nock_of_eqn_K hK⟩

/-- **`nock_predS_sound_nock`** (M4d's statement closed): acceptance on the
    skeleton's bits shows `*[sk.fill bs f] = p`. -/
theorem nock_predS_sound_nock {f p : Noun} {sk : Skel} {bs : List Bool} (hok : sk.ok = true)
    (hl : bs.length = sk.width) (h : Eval (nockPredS f sk ⬝ encNoun p ⬝ boolsT bs) K) :
    NockEval (sk.fill bs) f (.val p) :=
  nock_of_eqn_K (nock_predS_sound hok hl h).1

/-- **`nock_pred2_sound_nock`**: acceptance on `2k` bits shows atoms
    `a, b < 2^k` with `*[[a b] f] = p`. -/
theorem nock_pred2_sound_nock {f p : Noun} {k : Nat} {bs : List Bool} (hk : 0 < k)
    (hl : bs.length = 2 * k) (h : Eval (nockPred2V f k ⬝ encNoun p ⬝ boolsT bs) K) :
    ∃ a b, a < 2 ^ k ∧ b < 2 ^ k ∧ NockEval (.cell (.atom a) (.atom b)) f (.val p) :=
  let ⟨a, b, ha, hb, hK, _, _⟩ := nock_pred2_sound hk hl h
  ⟨a, b, ha, hb, nock_of_eqn_K hK⟩

end Nock2Ski
