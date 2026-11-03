import Nock2Ski.InterpEnc

open Nock
open Term

/-!
# The simulation: `NockEval` carried to weak reduction

Milestones M2 and M3 of `PLAN.md`, §2.4.  For every lean-nock derivation
`NockEval s f o` and every encoding `es` of the subject (`Enc s es`,
`Nock2Ski/Enc.lean`), the compiled program `nockToSki f ⬝ es` weakly
reduces as the outcome says, and so does the interpreter on any encoding
`ef` of the formula (`Enc f ef`):

- `embed_crash`: `o = .exit` gives `nockToSki f ⬝ es ↠ Err`;
  `nockI_crash`: and `nockI ⬝ es ⬝ ef ↠ Err`.
- `embed_value`: `o = .val p` gives `nockToSki f ⬝ es ↠ ep` for some
  encoding `ep` of `p`; `nockI_value`: and `nockI ⬝ es ⬝ ef ↠ ep'` for some
  encoding `ep'`.

M2 proved `embed_value` with an `Err` disjunct, because M1's `app` crashed
on a formula that reached opcode 2 or 9 as a plain `Cell` (assembled by
autocons or edit, or read from a code-free subject).  M3's `app` hands
such a cell to the interpreter `nockI` (`app_cell`), so the disjunct is
gone: the SKI term computes exactly Nock's value and crashes exactly where
Nock crashes, on all of Nock 4K.

## One induction for both

The two statements are mutual through `app`: the compiled code of opcode 2
or 9 on a plain `Cell` calls `nockI` (`app_cell`), and `nockI` on a `Form`
met in formula position runs its compiled code (`nockI_form`), which is
the compiled statement **at the same derivation node**.  So `embed_both`
proves, by a single induction on the `NockEval` derivation, the
conjunction: for every encoding of the subject, the compiled term
simulates, and for every encoding of the formula the interpreter does.
The compiled half of each case is M2's proof with `app_sim` now using the
interpreter's half of the hypothesis for opcode 2 and 9 on a `Cell`; the
interpreter half is `both_cell`: a `Form` reduces to the compiled half
just proved, a `Cell` dispatches on the opcode (`interp_op`) and follows
the branch (`nockO_O2`, …) with `force_sim` and the hypotheses, as the
compiled half does.  A mutual induction would have to state the compiled
half for the formula's own code and the interpreter half for the
derivation's sub-formulas with the same induction hypotheses, which is
exactly this conjunction, so the single induction is the natural shape.

`Sim o e` is the conclusion for one outcome, strong: a crash reduces to
`Err`, a value to an encoding of it.
-/

set_option maxRecDepth 4000

namespace Nock2Ski

local notation "v0" => OTerm.var 0
local notation "v1" => OTerm.var 1
local notation "v2" => OTerm.var 2
local notation "v3" => OTerm.var 3
local notation "v4" => OTerm.var 4

-- ---------------------------------------------------------------------------
-- β for the compiled λs
-- ---------------------------------------------------------------------------

/-- `λs. M` applied: `M` with `s` for the variable `0`. -/
theorem lamS_beta (M : OTerm) (s : Term) : WSteps (lamS M ⬝ s) (M.close (updC (fun _ => K) 0 s)) :=
  abs_beta_close 0 M (fun _ => K) s

theorem consK_beta (e x : Term) : WSteps (consK ⬝ e ⬝ x) (forceT ⬝ e ⬝ (CellC ⬝ x)) := by
  have h := absN_beta_close [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ (CellC.toO ⬝ₒ v1)) (fun _ => K) [e, x] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appK_beta (e x : Term) :
    ∃ kx, WSteps (appK ⬝ e ⬝ x) (forceT ⬝ e ⬝ kx) ∧ ∀ g, WSteps (kx ⬝ g) (appT ⬝ g ⬝ x) := by
  have h := absN_beta_close [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ absN [2] (appT.toO ⬝ₒ v2 ⬝ₒ v1))
    (fun _ => K) [e, x] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  refine ⟨_, h, fun g => ?_⟩
  have h2 := abs_beta_close 2 (appT.toO ⬝ₒ v2 ⬝ₒ v1) (updC (updC (fun _ => K) 0 e) 1 x) g
  simp only [close_app, close_var, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h2
  exact h2

theorem eqK_beta (e x : Term) : WSteps (eqK ⬝ e ⬝ x) (forceT ⬝ e ⬝ (eqT ⬝ x)) := by
  have h := absN_beta_close [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ (eqT.toO ⬝ₒ v1)) (fun _ => K) [e, x] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem pushK_beta (c s x : Term) : WSteps (pushK ⬝ c ⬝ s ⬝ x) (c ⬝ (CellC ⬝ x ⬝ s)) := by
  have h := absN_beta_close [0, 1, 2] (v0 ⬝ₒ (CellC.toO ⬝ₒ v2 ⬝ₒ v1)) (fun _ => K) [c, s, x] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem pullK_zero (core : Term) : WSteps (pullK (.atom 0) ⬝ core) (appT ⬝ errT ⬝ core) := by
  have h := abs_beta_close 0 (appT.toO ⬝ₒ axisO 0 v0 ⬝ₒ v0) (fun _ => K) core
  simp only [axisO, close_app, close_var, close_toO, updC, ↓reduceIte] at h
  exact h

theorem pullK_succ (k : Nat) (core : Term) :
    WSteps (pullK (.atom (k + 1)) ⬝ core) (appT ⬝ pickT core (axisPath (k + 1)) ⬝ core) := by
  have h := abs_beta_close 0 (appT.toO ⬝ₒ axisO (k + 1) v0 ⬝ₒ v0) (fun _ => K) core
  simp only [axisO, close_pickO, close_app, close_var, close_toO, updC, ↓reduceIte] at h
  exact h

theorem editK_beta (b : Noun) (c t : Term) :
    ∃ kv, WSteps (editK b ⬝ c ⬝ t) (forceT ⬝ c ⬝ kv) ∧ ∀ v, WSteps (kv ⬝ v) (editAx b ⬝ v ⬝ t) := by
  have h := absN_beta_close [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ absN [2] ((editAx b).toO ⬝ₒ v2 ⬝ₒ v1))
    (fun _ => K) [c, t] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  refine ⟨_, h, fun v => ?_⟩
  have h2 := abs_beta_close 2 ((editAx b).toO ⬝ₒ v2 ⬝ₒ v1) (updC (updC (fun _ => K) 0 c) 1 t) v
  simp only [close_app, close_var, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h2
  exact h2

-- ---------------------------------------------------------------------------
-- The edit walk: compile.py's `edit` along a path, over `Enc`
-- ---------------------------------------------------------------------------

/-- One level of `editT`: force the head, the tail, the rebuilt subtree,
    then `Cell`. -/
theorem editT_false (bs : List Bool) (v cur : Term) :
    ∃ k1, WSteps (editT (false :: bs) ⬝ v ⬝ cur) (forceT ⬝ (hdT ⬝ cur) ⬝ k1) ∧
      ∀ h, ∃ k2, WSteps (k1 ⬝ h) (forceT ⬝ (tlT ⬝ cur) ⬝ k2) ∧
        ∀ tl, ∃ k3, WSteps (k2 ⬝ tl) (forceT ⬝ (editT bs ⬝ v ⬝ h) ⬝ k3) ∧
          ∀ i, WSteps (k3 ⬝ i) (CellC ⬝ i ⬝ tl) := by
  have h := absN_beta_close [0, 1]
    (forceT.toO ⬝ₒ (hdT.toO ⬝ₒ v1) ⬝ₒ absN [2]
      (forceT.toO ⬝ₒ (tlT.toO ⬝ₒ v1) ⬝ₒ absN [3]
        (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v2) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v4 ⬝ₒ v3))))
    (fun _ => K) [v, cur] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, ↓reduceIte] at h
  refine ⟨_, h, fun hd => ?_⟩
  have h2 := abs_beta_close 2
    (forceT.toO ⬝ₒ (tlT.toO ⬝ₒ v1) ⬝ₒ absN [3]
      (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v2) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v4 ⬝ₒ v3)))
    (updC (updC (fun _ => K) 0 v) 1 cur) hd
  simp only [close_app, close_var, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h2
  refine ⟨_, h2, fun tl => ?_⟩
  have h3 := abs_beta_close 3
    (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v2) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v4 ⬝ₒ v3))
    (updC (updC (updC (fun _ => K) 0 v) 1 cur) 2 hd) tl
  simp only [close_app, close_var, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h3
  refine ⟨_, h3, fun i => ?_⟩
  have h4 := abs_beta_close 4 (CellC.toO ⬝ₒ v4 ⬝ₒ v3)
    (updC (updC (updC (updC (fun _ => K) 0 v) 1 cur) 2 hd) 3 tl) i
  simp only [close_app, close_var, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h4
  exact h4

theorem editT_true (bs : List Bool) (v cur : Term) :
    ∃ k1, WSteps (editT (true :: bs) ⬝ v ⬝ cur) (forceT ⬝ (hdT ⬝ cur) ⬝ k1) ∧
      ∀ h, ∃ k2, WSteps (k1 ⬝ h) (forceT ⬝ (tlT ⬝ cur) ⬝ k2) ∧
        ∀ tl, ∃ k3, WSteps (k2 ⬝ tl) (forceT ⬝ (editT bs ⬝ v ⬝ tl) ⬝ k3) ∧
          ∀ i, WSteps (k3 ⬝ i) (CellC ⬝ h ⬝ i) := by
  have h := absN_beta_close [0, 1]
    (forceT.toO ⬝ₒ (hdT.toO ⬝ₒ v1) ⬝ₒ absN [2]
      (forceT.toO ⬝ₒ (tlT.toO ⬝ₒ v1) ⬝ₒ absN [3]
        (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v3) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v2 ⬝ₒ v4))))
    (fun _ => K) [v, cur] rfl
  simp only [_root_.appT, close_app, close_var, close_toO, overrideC, updC, ↓reduceIte] at h
  refine ⟨_, h, fun hd => ?_⟩
  have h2 := abs_beta_close 2
    (forceT.toO ⬝ₒ (tlT.toO ⬝ₒ v1) ⬝ₒ absN [3]
      (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v3) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v2 ⬝ₒ v4)))
    (updC (updC (fun _ => K) 0 v) 1 cur) hd
  simp only [close_app, close_var, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h2
  refine ⟨_, h2, fun tl => ?_⟩
  have h3 := abs_beta_close 3
    (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v3) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v2 ⬝ₒ v4))
    (updC (updC (updC (fun _ => K) 0 v) 1 cur) 2 hd) tl
  simp only [close_app, close_var, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h3
  refine ⟨_, h3, fun i => ?_⟩
  have h4 := abs_beta_close 4 (CellC.toO ⬝ₒ v2 ⬝ₒ v4)
    (updC (updC (updC (updC (fun _ => K) 0 v) 1 cur) 2 hd) 3 tl) i
  simp only [close_app, close_var, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h4
  exact h4

/-- **The edit walk** meets `editP`: compile.py's `edit` at a static axis
    rebuilds the path with forced projections, and crashes into an atom. -/
theorem editT_enc : ∀ (bs : List Bool) {v t : Noun} {ev et : Term}, Enc v ev → Enc t et →
    Meets (editP v bs t) (editT bs ⬝ ev ⬝ et)
  | [], v, t, ev, et, hv, _ => ⟨ev, hv, .single (.K _ _)⟩
  | false :: bs, v, t, ev, et, hv, ht => by
    obtain ⟨k1, h1, hk1⟩ := editT_false bs ev et
    refine Meets.back h1 ?_
    cases t with
    | atom n =>
      show WSteps _ errT
      exact (WSteps.left _ (WSteps.right _ (hd_enc_atom ht))).trans (force_err _)
    | cell l r =>
      obtain ⟨el, hl, hhd⟩ := hd_enc ht
      obtain ⟨er, hr, htl⟩ := tl_enc ht
      obtain ⟨k2, h2, hk2⟩ := hk1 el
      obtain ⟨k3, h3, hk3⟩ := hk2 er
      have ih := editT_enc bs hv hl
      refine Meets.back ((WSteps.left _ (WSteps.right _ hhd)).trans ((force_enc hl k1).trans
        (h2.trans ((WSteps.left _ (WSteps.right _ htl)).trans ((force_enc hr k2).trans h3))))) ?_
      show Meets ((editP v bs l).map (fun l' => Noun.cell l' r)) _
      cases hE : editP v bs l with
      | none =>
        rw [hE] at ih
        exact (WSteps.left _ (WSteps.right _ ih)).trans (force_err _)
      | some r' =>
        rw [hE] at ih
        obtain ⟨ei, hi, hei⟩ := ih
        exact ⟨cellT ei er, .cell hi hr, (WSteps.left _ (WSteps.right _ hei)).trans
          ((force_enc hi k3).trans ((hk3 ei).trans (CellC_red ei er)))⟩
  | true :: bs, v, t, ev, et, hv, ht => by
    obtain ⟨k1, h1, hk1⟩ := editT_true bs ev et
    refine Meets.back h1 ?_
    cases t with
    | atom n =>
      show WSteps _ errT
      exact (WSteps.left _ (WSteps.right _ (hd_enc_atom ht))).trans (force_err _)
    | cell l r =>
      obtain ⟨el, hl, hhd⟩ := hd_enc ht
      obtain ⟨er, hr, htl⟩ := tl_enc ht
      obtain ⟨k2, h2, hk2⟩ := hk1 el
      obtain ⟨k3, h3, hk3⟩ := hk2 er
      have ih := editT_enc bs hv hr
      refine Meets.back ((WSteps.left _ (WSteps.right _ hhd)).trans ((force_enc hl k1).trans
        (h2.trans ((WSteps.left _ (WSteps.right _ htl)).trans ((force_enc hr k2).trans h3))))) ?_
      show Meets ((editP v bs r).map (fun r' => Noun.cell l r')) _
      cases hE : editP v bs r with
      | none =>
        rw [hE] at ih
        exact (WSteps.left _ (WSteps.right _ ih)).trans (force_err _)
      | some r' =>
        rw [hE] at ih
        obtain ⟨ei, hi, hei⟩ := ih
        exact ⟨cellT el ei, .cell hl hi, (WSteps.left _ (WSteps.right _ hei)).trans
          ((force_enc hi k3).trans ((hk3 ei).trans (CellC_red el ei)))⟩

/-- `editAx` meets `haxO`. -/
theorem editAx_enc {b r1 r2 : Noun} {e1 e2 : Term} (h1 : Enc r1 e1) (h2 : Enc r2 e2) :
    Meets (haxO b r1 r2) (editAx b ⬝ e1 ⬝ e2) := by
  cases b with
  | cell p q =>
    rw [haxO_cell]
    exact .step (.left _ (.K _ _)) (.single (.K _ _))
  | atom n =>
    cases n with
    | zero =>
      rw [haxO_zero]
      exact .step (.left _ (.K _ _)) (.single (.K _ _))
    | succ k =>
      rw [haxO_axisPath _ _ _ (by omega)]
      exact editT_enc _ h1 h2

-- ---------------------------------------------------------------------------
-- The step lemmas: one per opcode
-- ---------------------------------------------------------------------------

/-- β for the compiled `λs`, then the closing computed. -/
macro "lamS_step" : tactic =>
  `(tactic| (refine (lamS_beta _ _).trans ?_
             simp only [axisO, close_pickO, close_app, close_var, close_toO, at0, updC, ↓reduceIte]
             try exact WSteps.refl _))

theorem step_malformed {f : Noun} (h : Malformed f = true) (s : Term) :
    WSteps (nockToSki f ⬝ s) errT := by
  rw [nockToSki_malformed h]
  exact .single (.K _ _)

theorem step_autocons (b c d : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.cell b c) d) ⬝ s)
      (forceT ⬝ (nockToSki (.cell b c) ⬝ s) ⬝ (consK ⬝ (nockToSki d ⬝ s))) := by
  rw [nockToSki]
  lamS_step

theorem step_op0_zero (s : Term) : WSteps (nockToSki (.cell (.atom 0) (.atom 0)) ⬝ s) errT := by
  rw [nockToSki]
  lamS_step

theorem step_op0 (k : Nat) (s : Term) :
    WSteps (nockToSki (.cell (.atom 0) (.atom (k + 1))) ⬝ s) (pickT s (axisPath (k + 1))) := by
  rw [nockToSki]
  lamS_step

theorem step_op0_cell (p q : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 0) (.cell p q)) ⬝ s) errT := by
  rw [nockToSki.eq_def]
  exact .single (.K _ _)

theorem step_op1 (r : Noun) (s : Term) : WSteps (nockToSki (.cell (.atom 1) r) ⬝ s) (encLit r) := by
  rw [nockToSki]
  exact .single (.K _ _)

theorem step_op2 (b c : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 2) (.cell b c)) ⬝ s)
      (forceT ⬝ (nockToSki b ⬝ s) ⬝ (appK ⬝ (nockToSki c ⬝ s))) := by
  rw [nockToSki]
  lamS_step

theorem step_op3 (b : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 3) b) ⬝ s) (celT ⬝ (nockToSki b ⬝ s)) := by
  rw [nockToSki]
  lamS_step

theorem step_op4 (b : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 4) b) ⬝ s) (incT ⬝ (nockToSki b ⬝ s)) := by
  rw [nockToSki]
  lamS_step

theorem step_op5 (b c : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 5) (.cell b c)) ⬝ s)
      (forceT ⬝ (nockToSki b ⬝ s) ⬝ (eqK ⬝ (nockToSki c ⬝ s))) := by
  rw [nockToSki]
  lamS_step

theorem step_op6 (b c d : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 6) (.cell b (.cell c d))) ⬝ s)
      (ifnT ⬝ (nockToSki b ⬝ s) ⬝ (nockToSki c ⬝ s) ⬝ (nockToSki d ⬝ s)) := by
  rw [nockToSki]
  lamS_step

theorem step_op7 (b c : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 7) (.cell b c)) ⬝ s)
      (forceT ⬝ (nockToSki b ⬝ s) ⬝ nockToSki c) := by
  rw [nockToSki]
  lamS_step

theorem step_op8 (b c : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 8) (.cell b c)) ⬝ s)
      (forceT ⬝ (nockToSki b ⬝ s) ⬝ (pushK ⬝ nockToSki c ⬝ s)) := by
  rw [nockToSki]
  lamS_step

theorem step_op9 (b c : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 9) (.cell b c)) ⬝ s)
      (forceT ⬝ (nockToSki c ⬝ s) ⬝ pullK b) := by
  rw [nockToSki]
  lamS_step

theorem step_op10 (b c d : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 10) (.cell (.cell b c) d)) ⬝ s)
      (forceT ⬝ (nockToSki d ⬝ s) ⬝ (editK b ⬝ (nockToSki c ⬝ s))) := by
  rw [nockToSki]
  lamS_step

theorem step_op11_static (t : Nat) (c : Noun) :
    nockToSki (.cell (.atom 11) (.cell (.atom t) c)) = nockToSki c := by
  rw [nockToSki]

theorem step_op11_dynamic (t h c : Noun) (s : Term) :
    WSteps (nockToSki (.cell (.atom 11) (.cell (.cell t h) c)) ⬝ s)
      (forceT ⬝ (nockToSki h ⬝ s) ⬝ (K ⬝ (nockToSki c ⬝ s))) := by
  rw [nockToSki]
  lamS_step

-- ---------------------------------------------------------------------------
-- The simulation
-- ---------------------------------------------------------------------------

/-- The conclusion for one outcome: a crash reduces to `Err`, a value to an
    encoding of it. -/
def Sim : Outcome → Term → Prop
  | .val p, e => ∃ ep, Enc p ep ∧ WSteps e ep
  | .exit, e => WSteps e errT

theorem Sim.back {o : Outcome} {e e' : Term} (h : WSteps e e') (hs : Sim o e') : Sim o e := by
  cases o with
  | exit => exact h.trans hs
  | val p =>
    obtain ⟨ep, hp, he⟩ := hs
    exact ⟨ep, hp, h.trans he⟩

theorem Sim.exit {e : Term} (h : WSteps e errT) : Sim .exit e := h

theorem Sim.val {p : Noun} {e ep : Term} (hp : Enc p ep) (h : WSteps e ep) : Sim (.val p) e :=
  ⟨ep, hp, h⟩

/-- `force` of an operand that simulates a value: the continuation runs on
    an encoding of it. -/
theorem force_sim {r : Noun} {t k : Term} {o : Outcome} (ht : Sim (.val r) t)
    (hk : ∀ e, Enc r e → Sim o (k ⬝ e)) : Sim o (forceT ⬝ t ⬝ k) := by
  obtain ⟨e, he, hte⟩ := ht
  exact Sim.back ((WSteps.left _ (WSteps.right _ hte)).trans (force_enc he k)) (hk e he)

/-- `force` of an operand that crashes. -/
theorem force_exit {t k : Term} (ht : WSteps t errT) : Sim .exit (forceT ⬝ t ⬝ k) :=
  (WSteps.left _ (WSteps.right _ ht)).trans (force_err k)

/-- An atom in formula position only crashes. -/
theorem atom_exit {s : Noun} {n : Nat} {o : Outcome} (h : NockEval s (.atom n) o) : o = .exit := by
  cases h; rfl

/-- The two halves of the statement at one node: the compiled term on an
    encoding of the subject, and the interpreter on an encoding of the
    formula. -/
def Both (s f : Noun) (o : Outcome) : Prop :=
  ∀ {es : Term}, Enc s es → Sim o (nockToSki f ⬝ es) ∧ ∀ {ef : Term}, Enc f ef → Sim o (nockIFix ⬝ es ⬝ ef)

/-- `app` of an encoded formula on an encoded subject simulates the
    evaluation: a `Form` runs its code, a `Cell` the interpreter, an atom
    crashes (and Nock crashes). -/
theorem app_sim {r2 r1 : Noun} {e2 e1 : Term} {o : Outcome} (h3 : NockEval r1 r2 o) (h2 : Enc r2 e2)
    (ih : Both r1 r2 o) (h1 : Enc r1 e1) : Sim o (appT ⬝ e2 ⬝ e1) := by
  cases r2 with
  | atom n =>
    rw [atom_exit h3]
    exact Sim.exit (app_enc_atom h2)
  | cell h t =>
    cases h2 with
    | cell hh ht =>
      exact Sim.back ((app_cell _ _ _).trans (WSteps.left _ (WSteps.left _ nockIT_fix))) ((ih h1).2 (.cell hh ht))
    | form hh ht => exact Sim.back (app_form _ _ _ _) (ih h1).1

/-- `appI` likewise, with the evaluator `nockI` itself passed in. -/
theorem appI_sim {r2 r1 : Noun} {e2 e1 : Term} {o : Outcome} (h3 : NockEval r1 r2 o) (h2 : Enc r2 e2)
    (ih : Both r1 r2 o) (h1 : Enc r1 e1) : Sim o (appIT ⬝ nockIFix ⬝ e2 ⬝ e1) := by
  cases r2 with
  | atom n =>
    rw [atom_exit h3, h2.atom_inv]
    exact Sim.exit (appI_atom _ _ _)
  | cell h t =>
    cases h2 with
    | cell hh ht => exact Sim.back (appI_cell _ _ _ _) ((ih h1).2 (.cell hh ht))
    | form hh ht => exact Sim.back (appI_form _ _ _ _ _) (ih h1).1

/-- Both halves at a cell formula: the interpreter on a `Form` is the
    compiled half, on a `Cell` the dispatch given. -/
theorem both_cell {fh ft : Noun} {o : Outcome} {es : Term} (hA : Sim o (nockToSki (.cell fh ft) ⬝ es))
    (hB : ∀ {eh et : Term}, Enc fh eh → Enc ft et → Sim o (nockIFix ⬝ es ⬝ cellT eh et)) :
    Sim o (nockToSki (.cell fh ft) ⬝ es) ∧ ∀ {ef : Term}, Enc (.cell fh ft) ef → Sim o (nockIFix ⬝ es ⬝ ef) := by
  refine ⟨hA, fun hef => ?_⟩
  cases hef with
  | cell hh ht => exact hB hh ht
  | form hh ht => exact Sim.back (nockI_form _ _ _ _) hA

/-- The interpreter's side of an opcode `k ≤ 12`: the head is the atom `k`. -/
theorem interp_at {k : Nat} (hk : k ≤ 12) {eh et : Term} (hh : Enc (.atom k) eh) {o : Outcome} {es : Term}
    (h : Sim o (nockOT ⬝ nockIFix ⬝ opC k ⬝ es ⬝ et)) : Sim o (nockIFix ⬝ es ⬝ cellT eh et) := by
  rw [hh.atom_inv]
  exact Sim.back (interp_op hk es et) h

-- ---------------------------------------------------------------------------
-- Malformed formulas: both halves crash
-- ---------------------------------------------------------------------------

/-- A malformed formula crashes on both sides: the compiled term is `Err`,
    the interpreter reaches `Err` through the shape checks (`cel2` on an
    atom, `op12`, `Obad`). -/
theorem malformed_both {s f : Noun} (hm : Malformed f = true) : Both s f .exit := by
  intro es hes
  have hA : Sim .exit (nockToSki f ⬝ es) := Sim.exit (step_malformed hm es)
  cases f with
  | atom n =>
    refine ⟨hA, fun hef => ?_⟩
    rw [hef.atom_inv]
    exact Sim.exit (nockI_atom _ _)
  | cell fh ft =>
    refine both_cell hA fun hh ht => ?_
    cases fh with
    | cell _ _ => simp [Malformed] at hm
    | atom k =>
      match k, ft, hm with
      | 0, _, hm | 1, _, hm | 3, _, hm | 4, _, hm => simp [Malformed] at hm
      | 2, .cell _ _, hm | 5, .cell _ _, hm | 7, .cell _ _, hm | 8, .cell _ _, hm
      | 9, .cell _ _, hm | 11, .cell _ _, hm | 6, .cell _ (.cell _ _), hm
      | 10, .cell (.cell _ _) _, hm => simp [Malformed] at hm
      | 2, .atom _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O2 _ _ _).trans (cel2_atom ht _)))
      | 5, .atom _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O5 _ _ _).trans (cel2_atom ht _)))
      | 7, .atom _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O7 _ _ _).trans (cel2_atom ht _)))
      | 8, .atom _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O8 _ _ _).trans (cel2_atom ht _)))
      | 9, .atom _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O9 _ _ _).trans (cel2_atom ht _)))
      | 11, .atom _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O11 _ _ _).trans (cel2_atom ht _)))
      | 6, .atom _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O6 _ _ _).trans (cel2_atom ht _)))
      | 6, .cell _ (.atom _), _ =>
        obtain ⟨eb, eyn, _, hyn, h1⟩ := cel2_enc ht (nockOK10 ⬝ nockIFix ⬝ es)
        exact interp_at (by decide) hh (Sim.exit ((nockO_O6 _ _ _).trans (h1.trans
          ((nockOK10_beta _ _ _ _).trans (cel2_atom hyn _)))))
      | 10, .atom _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O10 _ _ _).trans (cel2_atom ht _)))
      | 10, .cell (.atom _) _, _ =>
        obtain ⟨ebc, ed, hbc, _, h1⟩ := cel2_enc ht (nockOK26 ⬝ nockIFix ⬝ es)
        exact interp_at (by decide) hh (Sim.exit ((nockO_O10 _ _ _).trans (h1.trans
          ((nockOK26_beta _ _ _ _).trans (cel2_atom hbc _)))))
      | 12, _, _ => exact interp_at (by decide) hh (Sim.exit ((nockO_O12 _ _ _).trans (op12T_beta _ _ _)))
      | k + 13, _, _ =>
        rw [hh.atom_inv]
        exact Sim.exit (interp_bad (by omega) es _)

-- ---------------------------------------------------------------------------
-- The simulation: one induction for the compiled term and the interpreter
-- ---------------------------------------------------------------------------

/-- **The simulation.**  Every lean-nock derivation is carried to weak
    reduction of the compiled program on any encoding of the subject, and
    of the interpreter on any encodings of the subject and the formula. -/
theorem embed_both {s f : Noun} {o : Outcome} (h : NockEval s f o) : Both s f o := by
  induction h with
  | crash_malformed hm => exact malformed_both hm
  -- autocons
  | @autocons a b c fol r1 r2 _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_autocons _ _ _ es) (force_sim (ih1 hes).1 fun e1 he1 => ?_)
      refine Sim.back (consK_beta _ _) (force_sim (ih2 hes).1 fun e2 he2 => ?_)
      exact Sim.val (.cell he1 he2) (CellC_red e1 e2)
    · refine Sim.back (interp_autocons hh es _) (force_sim ((ih1 hes).2 hh) fun e1 he1 => ?_)
      refine Sim.back (autoconsK1_beta _ _ _ _) (force_sim ((ih2 hes).2 ht) fun e2 he2 => ?_)
      exact Sim.val (.cell he1 he2) (autoconsK0_cell e1 e2)
  | @autocons_crashL a b c fol _ ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_autocons _ _ _ es) (force_exit (ih1 hes).1)
    · exact Sim.back (interp_autocons hh es _) (force_exit ((ih1 hes).2 hh))
  | @autocons_crashR a b c fol r1 _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_autocons _ _ _ es) (force_sim (ih1 hes).1 fun e1 _ => ?_)
      exact Sim.back (consK_beta _ _) (force_exit (ih2 hes).1)
    · refine Sim.back (interp_autocons hh es _) (force_sim ((ih1 hes).2 hh) fun e1 _ => ?_)
      exact Sim.back (autoconsK1_beta _ _ _ _) (force_exit ((ih2 hes).2 ht))
  -- 0
  | @op0 a fol r hfas =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · cases fol with
      | cell p q => rw [fasO_cell] at hfas; cases hfas
      | atom n =>
        cases n with
        | zero => rw [fasO_zero] at hfas; cases hfas
        | succ k =>
          rw [fasO_axisPath _ _ (by omega)] at hfas
          obtain ⟨er, her, hp⟩ := pick_enc _ r hfas hes (.refl es)
          exact Sim.val her ((step_op0 k es).trans hp)
    · refine interp_at (by decide) hh (Sim.back (nockO_O0 _ _ _) ?_)
      cases fol with
      | cell p q => rw [fasO_cell] at hfas; cases hfas
      | atom n =>
        rw [ht.atom_inv]
        obtain ⟨er, her, hp⟩ := slotB_enc hfas hes
        exact Sim.val her ((atomT_elim _ _ _ _ _).trans ((nockOK0_beta _ _).trans hp))
  | @op0_crash a fol hfas =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · cases fol with
      | cell p q => exact Sim.exit (step_op0_cell p q es)
      | atom n =>
        cases n with
        | zero => exact Sim.exit (step_op0_zero es)
        | succ k =>
          rw [fasO_axisPath _ _ (by omega)] at hfas
          exact Sim.exit ((step_op0 k es).trans (pick_enc_none _ hfas hes (.refl es)))
    · refine interp_at (by decide) hh (Sim.back (nockO_O0 _ _ _) ?_)
      cases fol with
      | cell p q =>
        cases ht with
        | cell _ _ => exact Sim.exit ((cellT_elim _ _ _ _ _ _).trans (nockOK1_beta _ _))
        | form _ _ => exact Sim.exit ((formT_elim _ _ _ _ _ _ _).trans (nockOK2_beta _ _ _))
      | atom n =>
        rw [ht.atom_inv]
        exact Sim.exit ((atomT_elim _ _ _ _ _).trans ((nockOK0_beta _ _).trans (slotB_none hfas hes)))
  -- 1
  | @op1 a fol =>
    intro es hes
    refine both_cell (Sim.val (enc_encLit _) (step_op1 _ es)) fun hh ht => ?_
    exact interp_at (by decide) hh (Sim.val ht (nockO_O1 _ _ _))
  -- 2
  | @op2 a b c r1 r2 o _ _ h3 ih1 ih2 ih3 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op2 _ _ es) (force_sim (ih1 hes).1 fun e1 he1 => ?_)
      obtain ⟨kx, hb, hkx⟩ := appK_beta (nockToSki _ ⬝ es) e1
      refine Sim.back hb (force_sim (ih2 hes).1 fun e2 he2 => Sim.back (hkx e2) ?_)
      exact app_sim h3 he2 ih3 he1
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK5 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O2 _ _ _).trans (h1.trans (nockOK5_beta _ _ _ _))) ?_)
      refine force_sim ((ih1 hes).2 hb) fun e1 he1 => Sim.back (nockOK4_beta _ _ _ _) ?_
      refine force_sim ((ih2 hes).2 hc) fun e2 he2 => Sim.back (nockOK3_beta _ _ _) ?_
      exact appI_sim h3 he2 ih3 he1
  | @op2_crashL a b c _ ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op2 _ _ es) (force_exit (ih1 hes).1)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK5 ⬝ nockIFix ⬝ es)
      exact interp_at (by decide) hh (Sim.back ((nockO_O2 _ _ _).trans (h1.trans (nockOK5_beta _ _ _ _)))
        (force_exit ((ih1 hes).2 hb)))
  | @op2_crashR a b c r1 _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op2 _ _ es) (force_sim (ih1 hes).1 fun e1 _ => ?_)
      obtain ⟨kx, hb, _⟩ := appK_beta (nockToSki _ ⬝ es) e1
      exact Sim.back hb (force_exit (ih2 hes).1)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK5 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O2 _ _ _).trans (h1.trans (nockOK5_beta _ _ _ _))) ?_)
      exact force_sim ((ih1 hes).2 hb) fun e1 _ => Sim.back (nockOK4_beta _ _ _ _) (force_exit ((ih2 hes).2 hc))
  -- 3
  | @op3 a fol r _ ih =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · obtain ⟨e, he, hB⟩ := (ih hes).1
      exact Sim.back (step_op3 _ es) (Sim.val (enc_encNoun _) ((WSteps.right _ hB).trans (cel_enc he)))
    · obtain ⟨e, he, hB⟩ := (ih hes).2 ht
      exact interp_at (by decide) hh (Sim.back (nockO_O3 _ _ _)
        (Sim.val (enc_encNoun _) ((WSteps.right _ hB).trans (cel_enc he))))
  | @op3_crash a fol _ ih =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op3 _ es) (Sim.exit ((WSteps.right _ (ih hes).1).trans cel_err))
    · exact interp_at (by decide) hh (Sim.back (nockO_O3 _ _ _)
        (Sim.exit ((WSteps.right _ ((ih hes).2 ht)).trans cel_err)))
  -- 4
  | @op4 a fol r v _ hl ih =>
    intro es hes
    cases r with
    | cell _ _ => rw [lusO_cell] at hl; cases hl
    | atom n =>
      rw [lusO_atom] at hl
      cases hl
      refine both_cell ?_ fun hh ht => ?_
      · obtain ⟨e, he, hB⟩ := (ih hes).1
        exact Sim.back (step_op4 _ es) (Sim.val (enc_encNoun _) ((WSteps.right _ hB).trans (inc_enc_atom he)))
      · obtain ⟨e, he, hB⟩ := (ih hes).2 ht
        exact interp_at (by decide) hh (Sim.back (nockO_O4 _ _ _)
          (Sim.val (enc_encNoun _) ((WSteps.right _ hB).trans (inc_enc_atom he))))
  | @op4_cell a fol r _ hl ih =>
    intro es hes
    cases r with
    | atom n => rw [lusO_atom] at hl; cases hl
    | cell _ _ =>
      refine both_cell ?_ fun hh ht => ?_
      · obtain ⟨e, he, hB⟩ := (ih hes).1
        exact Sim.back (step_op4 _ es) (Sim.exit ((WSteps.right _ hB).trans (inc_enc_cell he)))
      · obtain ⟨e, he, hB⟩ := (ih hes).2 ht
        exact interp_at (by decide) hh (Sim.back (nockO_O4 _ _ _)
          (Sim.exit ((WSteps.right _ hB).trans (inc_enc_cell he))))
  | @op4_crash a fol _ ih =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op4 _ es) (Sim.exit ((WSteps.right _ (ih hes).1).trans inc_err))
    · exact interp_at (by decide) hh (Sim.back (nockO_O4 _ _ _)
        (Sim.exit ((WSteps.right _ ((ih hes).2 ht)).trans inc_err)))
  -- 5
  | @op5 a b c r1 r2 _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op5 _ _ es) (force_sim (ih1 hes).1 fun e1 he1 => ?_)
      refine Sim.back (eqK_beta _ _) (force_sim (ih2 hes).1 fun e2 he2 => ?_)
      exact Sim.val (enc_encNoun _) (eq_enc he1 he2)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK8 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O5 _ _ _).trans (h1.trans (nockOK8_beta _ _ _ _))) ?_)
      refine force_sim ((ih1 hes).2 hb) fun e1 he1 => Sim.back (nockOK7_beta _ _ _ _) ?_
      refine force_sim ((ih2 hes).2 hc) fun e2 he2 => Sim.back (nockOK6_beta _ _) ?_
      exact Sim.val (enc_encNoun _) (eq_enc he1 he2)
  | @op5_crashL a b c _ ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op5 _ _ es) (force_exit (ih1 hes).1)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK8 ⬝ nockIFix ⬝ es)
      exact interp_at (by decide) hh (Sim.back ((nockO_O5 _ _ _).trans (h1.trans (nockOK8_beta _ _ _ _)))
        (force_exit ((ih1 hes).2 hb)))
  | @op5_crashR a b c r1 _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op5 _ _ es) (force_sim (ih1 hes).1 fun e1 _ => ?_)
      exact Sim.back (eqK_beta _ _) (force_exit (ih2 hes).1)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK8 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O5 _ _ _).trans (h1.trans (nockOK8_beta _ _ _ _))) ?_)
      exact force_sim ((ih1 hes).2 hb) fun e1 _ => Sim.back (nockOK7_beta _ _ _ _) (force_exit ((ih2 hes).2 hc))
  -- 6
  | @op6_then a b c d o _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · obtain ⟨e, he, hB⟩ := (ih1 hes).1
      exact Sim.back (step_op6 _ _ _ es) (Sim.back ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans
        (ifn_enc_zero he _ _)) (ih2 hes).1)
    · obtain ⟨eb, ecd, hb, hcd, h1⟩ := cel2_enc ht (nockOK10 ⬝ nockIFix ⬝ es)
      obtain ⟨ec, ed, hc, hd, h2⟩ := cel2_enc hcd (nockOK9 ⬝ nockIFix ⬝ es ⬝ eb)
      obtain ⟨e, he, hB⟩ := (ih1 hes).2 hb
      refine interp_at (by decide) hh (Sim.back ((nockO_O6 _ _ _).trans (h1.trans ((nockOK10_beta _ _ _ _).trans
        (h2.trans (nockOK9_beta _ _ _ _ _))))) ?_)
      exact Sim.back ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans (ifn_enc_zero he _ _)) ((ih2 hes).2 hc)
  | @op6_else a b c d o _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · obtain ⟨e, he, hB⟩ := (ih1 hes).1
      exact Sim.back (step_op6 _ _ _ es) (Sim.back ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans
        (ifn_enc_one he _ _)) (ih2 hes).1)
    · obtain ⟨eb, ecd, hb, hcd, h1⟩ := cel2_enc ht (nockOK10 ⬝ nockIFix ⬝ es)
      obtain ⟨ec, ed, hc, hd, h2⟩ := cel2_enc hcd (nockOK9 ⬝ nockIFix ⬝ es ⬝ eb)
      obtain ⟨e, he, hB⟩ := (ih1 hes).2 hb
      refine interp_at (by decide) hh (Sim.back ((nockO_O6 _ _ _).trans (h1.trans ((nockOK10_beta _ _ _ _).trans
        (h2.trans (nockOK9_beta _ _ _ _ _))))) ?_)
      exact Sim.back ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans (ifn_enc_one he _ _)) ((ih2 hes).2 hd)
  | @op6_nonloob a b c d r _ h0 h1 ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · obtain ⟨e, he, hB⟩ := (ih1 hes).1
      exact Sim.back (step_op6 _ _ _ es) (Sim.exit ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans
        (ifn_enc_crash he h0 h1 _ _)))
    · obtain ⟨eb, ecd, hb, hcd, hc1⟩ := cel2_enc ht (nockOK10 ⬝ nockIFix ⬝ es)
      obtain ⟨ec, ed, hc, hd, hc2⟩ := cel2_enc hcd (nockOK9 ⬝ nockIFix ⬝ es ⬝ eb)
      obtain ⟨e, he, hB⟩ := (ih1 hes).2 hb
      refine interp_at (by decide) hh (Sim.back ((nockO_O6 _ _ _).trans (hc1.trans ((nockOK10_beta _ _ _ _).trans
        (hc2.trans (nockOK9_beta _ _ _ _ _))))) ?_)
      exact Sim.exit ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans (ifn_enc_crash he h0 h1 _ _))
  | @op6_crash a b c d _ ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op6 _ _ _ es)
        (Sim.exit ((WSteps.left _ (WSteps.left _ (WSteps.right _ (ih1 hes).1))).trans (ifn_err _ _)))
    · obtain ⟨eb, ecd, hb, hcd, hc1⟩ := cel2_enc ht (nockOK10 ⬝ nockIFix ⬝ es)
      obtain ⟨ec, ed, hc, hd, hc2⟩ := cel2_enc hcd (nockOK9 ⬝ nockIFix ⬝ es ⬝ eb)
      refine interp_at (by decide) hh (Sim.back ((nockO_O6 _ _ _).trans (hc1.trans ((nockOK10_beta _ _ _ _).trans
        (hc2.trans (nockOK9_beta _ _ _ _ _))))) ?_)
      exact Sim.exit ((WSteps.left _ (WSteps.left _ (WSteps.right _ ((ih1 hes).2 hb)))).trans (ifn_err _ _))
  -- 7
  | @op7 a b c r1 o _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op7 _ _ es) (force_sim (ih1 hes).1 fun e1 he1 => (ih2 he1).1)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK12 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O7 _ _ _).trans (h1.trans (nockOK12_beta _ _ _ _))) ?_)
      exact force_sim ((ih1 hes).2 hb) fun e1 he1 => Sim.back (nockOK11_beta _ _ _) ((ih2 he1).2 hc)
  | @op7_crash a b c _ ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op7 _ _ es) (force_exit (ih1 hes).1)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK12 ⬝ nockIFix ⬝ es)
      exact interp_at (by decide) hh (Sim.back ((nockO_O7 _ _ _).trans (h1.trans (nockOK12_beta _ _ _ _)))
        (force_exit ((ih1 hes).2 hb)))
  -- 8
  | @op8 a b c r1 o _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op8 _ _ es) (force_sim (ih1 hes).1 fun e1 he1 => ?_)
      exact Sim.back ((pushK_beta _ _ _).trans (WSteps.right _ (CellC_red e1 es))) (ih2 (.cell he1 hes)).1
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK14 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O8 _ _ _).trans (h1.trans (nockOK14_beta _ _ _ _))) ?_)
      refine force_sim ((ih1 hes).2 hb) fun e1 he1 => ?_
      exact Sim.back ((nockOK13_beta _ _ _ _).trans (WSteps.left _ (WSteps.right _ (CellC_red e1 es))))
        ((ih2 (.cell he1 hes)).2 hc)
  | @op8_crash a b c _ ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op8 _ _ es) (force_exit (ih1 hes).1)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK14 ⬝ nockIFix ⬝ es)
      exact interp_at (by decide) hh (Sim.back ((nockO_O8 _ _ _).trans (h1.trans (nockOK14_beta _ _ _ _)))
        (force_exit ((ih1 hes).2 hb)))
  -- 9
  | @op9 a b c core arm o _ hfas h3 ih1 ih3 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op9 _ _ es) (force_sim (ih1 hes).1 fun ec hec => ?_)
      cases b with
      | cell p q => rw [fasO_cell] at hfas; cases hfas
      | atom n =>
        cases n with
        | zero => rw [fasO_zero] at hfas; cases hfas
        | succ k =>
          rw [fasO_axisPath _ _ (by omega)] at hfas
          obtain ⟨ea, hea, hp⟩ := pick_enc _ arm hfas hec (.refl ec)
          refine Sim.back ((pullK_succ k ec).trans (WSteps.left _ (WSteps.right _ hp))) ?_
          exact app_sim h3 hea ih3 hec
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK19 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O9 _ _ _).trans (h1.trans (nockOK19_beta _ _ _ _))) ?_)
      refine force_sim ((ih1 hes).2 hc) fun ecore hcore => Sim.back (nockOK18_beta _ _ _) ?_
      cases b with
      | cell p q => rw [fasO_cell] at hfas; cases hfas
      | atom n =>
        rw [hb.atom_inv]
        obtain ⟨ea, hea, hsl⟩ := slotB_enc hfas hcore
        refine Sim.back ((atomT_elim _ _ _ _ _).trans ((nockOK15_beta _ _ _).trans
          (WSteps.left _ (WSteps.right _ hsl)))) ?_
        exact appI_sim h3 hea ih3 hcore
  | @op9_badaxis a b c core _ hfas ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op9 _ _ es) (force_sim (ih1 hes).1 fun ec hec => ?_)
      cases b with
      | cell p q => exact Sim.exit (.single (.K _ _))
      | atom n =>
        cases n with
        | zero => exact Sim.exit ((pullK_zero ec).trans (app_err ec))
        | succ k =>
          rw [fasO_axisPath _ _ (by omega)] at hfas
          exact Sim.exit ((pullK_succ k ec).trans
            ((WSteps.left _ (WSteps.right _ (pick_enc_none _ hfas hec (.refl ec)))).trans (app_err ec)))
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK19 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O9 _ _ _).trans (h1.trans (nockOK19_beta _ _ _ _))) ?_)
      refine force_sim ((ih1 hes).2 hc) fun ecore hcore => Sim.back (nockOK18_beta _ _ _) ?_
      cases b with
      | cell p q =>
        cases hb with
        | cell _ _ => exact Sim.exit ((cellT_elim _ _ _ _ _ _).trans (nockOK16_beta _ _))
        | form _ _ => exact Sim.exit ((formT_elim _ _ _ _ _ _ _).trans (nockOK17_beta _ _ _))
      | atom n =>
        rw [hb.atom_inv]
        exact Sim.exit ((atomT_elim _ _ _ _ _).trans ((nockOK15_beta _ _ _).trans
          ((WSteps.left _ (WSteps.right _ (slotB_none hfas hcore))).trans (appI_err _ _))))
  | @op9_crash a b c _ ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op9 _ _ es) (force_exit (ih1 hes).1)
    · obtain ⟨eb, ec, hb, hc, h1⟩ := cel2_enc ht (nockOK19 ⬝ nockIFix ⬝ es)
      exact interp_at (by decide) hh (Sim.back ((nockO_O9 _ _ _).trans (h1.trans (nockOK19_beta _ _ _ _)))
        (force_exit ((ih1 hes).2 hc)))
  -- 10
  | @op10 a b c d r1 r2 v _ _ hhax ihd ihc =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op10 _ _ _ es) (force_sim (ihd hes).1 fun e2 he2 => ?_)
      obtain ⟨kv, hb, hkv⟩ := editK_beta b (nockToSki c ⬝ es) e2
      refine Sim.back hb (force_sim (ihc hes).1 fun e1 he1 => Sim.back (hkv e1) ?_)
      have hm := editAx_enc (b := b) he1 he2
      rw [hhax] at hm
      obtain ⟨ew, hw, hew⟩ := hm
      exact Sim.val hw hew
    · obtain ⟨ebc, ed, hbc, hd, h1⟩ := cel2_enc ht (nockOK26 ⬝ nockIFix ⬝ es)
      obtain ⟨eb, ec, hb, hc, h2⟩ := cel2_enc hbc (nockOK25 ⬝ nockIFix ⬝ es ⬝ ed)
      refine interp_at (by decide) hh (Sim.back ((nockO_O10 _ _ _).trans (h1.trans ((nockOK26_beta _ _ _ _).trans
        (h2.trans (nockOK25_beta _ _ _ _ _))))) ?_)
      refine force_sim ((ihd hes).2 hd) fun eu hu => Sim.back (nockOK24_beta _ _ _ _ _) ?_
      refine force_sim ((ihc hes).2 hc) fun ev' hv => Sim.back (nockOK23_beta _ _ _) ?_
      cases b with
      | cell p q => rw [haxO_cell] at hhax; cases hhax
      | atom n =>
        rw [hb.atom_inv]
        have hm := editB_enc (n := n) hv hu
        rw [hhax] at hm
        obtain ⟨ew, hw, hew⟩ := hm
        exact Sim.val hw ((atomT_elim _ _ _ _ _).trans ((nockOK20_beta _ _ _).trans hew))
  | @op10_badaxis a b c d r1 r2 _ _ hhax ihd ihc =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op10 _ _ _ es) (force_sim (ihd hes).1 fun e2 he2 => ?_)
      obtain ⟨kv, hb, hkv⟩ := editK_beta b (nockToSki c ⬝ es) e2
      refine Sim.back hb (force_sim (ihc hes).1 fun e1 he1 => Sim.back (hkv e1) ?_)
      have hm := editAx_enc (b := b) he1 he2
      rw [hhax] at hm
      exact Sim.exit hm
    · obtain ⟨ebc, ed, hbc, hd, h1⟩ := cel2_enc ht (nockOK26 ⬝ nockIFix ⬝ es)
      obtain ⟨eb, ec, hb, hc, h2⟩ := cel2_enc hbc (nockOK25 ⬝ nockIFix ⬝ es ⬝ ed)
      refine interp_at (by decide) hh (Sim.back ((nockO_O10 _ _ _).trans (h1.trans ((nockOK26_beta _ _ _ _).trans
        (h2.trans (nockOK25_beta _ _ _ _ _))))) ?_)
      refine force_sim ((ihd hes).2 hd) fun eu hu => Sim.back (nockOK24_beta _ _ _ _ _) ?_
      refine force_sim ((ihc hes).2 hc) fun ev' hv => Sim.back (nockOK23_beta _ _ _) ?_
      cases b with
      | cell p q =>
        cases hb with
        | cell _ _ => exact Sim.exit ((cellT_elim _ _ _ _ _ _).trans (nockOK21_beta _ _))
        | form _ _ => exact Sim.exit ((formT_elim _ _ _ _ _ _ _).trans (nockOK22_beta _ _ _))
      | atom n =>
        rw [hb.atom_inv]
        have hm := editB_enc (n := n) hv hu
        rw [hhax] at hm
        exact Sim.exit ((atomT_elim _ _ _ _ _).trans ((nockOK20_beta _ _ _).trans hm))
  | @op10_crashTree a b c d _ ihd =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op10 _ _ _ es) (force_exit (ihd hes).1)
    · obtain ⟨ebc, ed, hbc, hd, h1⟩ := cel2_enc ht (nockOK26 ⬝ nockIFix ⬝ es)
      obtain ⟨eb, ec, hb, hc, h2⟩ := cel2_enc hbc (nockOK25 ⬝ nockIFix ⬝ es ⬝ ed)
      exact interp_at (by decide) hh (Sim.back ((nockO_O10 _ _ _).trans (h1.trans ((nockOK26_beta _ _ _ _).trans
        (h2.trans (nockOK25_beta _ _ _ _ _))))) (force_exit ((ihd hes).2 hd)))
  | @op10_crashPatch a b c d r2 _ _ ihd ihc =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op10 _ _ _ es) (force_sim (ihd hes).1 fun e2 _ => ?_)
      obtain ⟨kv, hb, _⟩ := editK_beta _ (nockToSki _ ⬝ es) e2
      exact Sim.back hb (force_exit (ihc hes).1)
    · obtain ⟨ebc, ed, hbc, hd, h1⟩ := cel2_enc ht (nockOK26 ⬝ nockIFix ⬝ es)
      obtain ⟨eb, ec, hb, hc, h2⟩ := cel2_enc hbc (nockOK25 ⬝ nockIFix ⬝ es ⬝ ed)
      refine interp_at (by decide) hh (Sim.back ((nockO_O10 _ _ _).trans (h1.trans ((nockOK26_beta _ _ _ _).trans
        (h2.trans (nockOK25_beta _ _ _ _ _))))) ?_)
      exact force_sim ((ihd hes).2 hd) fun eu _ => Sim.back (nockOK24_beta _ _ _ _ _) (force_exit ((ihc hes).2 hc))
  -- 11
  | @op11_static a t c o _ ih =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · rw [step_op11_static]; exact (ih hes).1
    · obtain ⟨eh, ec, hh', hc, h1⟩ := cel2_enc ht (nockOK32 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O11 _ _ _).trans (h1.trans (nockOK32_beta _ _ _ _))) ?_)
      rw [hh'.atom_inv]
      exact Sim.back ((atomT_elim _ _ _ _ _).trans (nockOK27_beta _ _ _ _)) ((ih hes).2 hc)
  | @op11_dynamic a t c d r1 o _ _ ih1 ih2 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · refine Sim.back (step_op11_dynamic _ _ _ es) (force_sim (ih1 hes).1 fun e1 _ => ?_)
      exact Sim.back (.single (.K _ _)) (ih2 hes).1
    · obtain ⟨etc, ed, htc, hd, h1⟩ := cel2_enc ht (nockOK32 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O11 _ _ _).trans (h1.trans (nockOK32_beta _ _ _ _))) ?_)
      cases htc with
      | @cell _ _ et' ec _ hc =>
        refine Sim.back ((cellT_elim _ _ _ _ _ _).trans (nockOK29_beta _ _ _ _ _)) ?_
        exact force_sim ((ih1 hes).2 hc) fun e1 _ => Sim.back (nockOK28_beta _ _ _ _) ((ih2 hes).2 hd)
      | @form _ _ et' ec _ hc =>
        refine Sim.back ((formT_elim _ _ _ _ _ _ _).trans (nockOK31_beta _ _ _ _ _ _)) ?_
        exact force_sim ((ih1 hes).2 hc) fun e1 _ => Sim.back (nockOK30_beta _ _ _ _) ((ih2 hes).2 hd)
  | @op11_dyn_crash a t c d _ ih1 =>
    intro es hes
    refine both_cell ?_ fun hh ht => ?_
    · exact Sim.back (step_op11_dynamic _ _ _ es) (force_exit (ih1 hes).1)
    · obtain ⟨etc, ed, htc, hd, h1⟩ := cel2_enc ht (nockOK32 ⬝ nockIFix ⬝ es)
      refine interp_at (by decide) hh (Sim.back ((nockO_O11 _ _ _).trans (h1.trans (nockOK32_beta _ _ _ _))) ?_)
      cases htc with
      | @cell _ _ et' ec _ hc =>
        exact Sim.back ((cellT_elim _ _ _ _ _ _).trans (nockOK29_beta _ _ _ _ _)) (force_exit ((ih1 hes).2 hc))
      | @form _ _ et' ec _ hc =>
        exact Sim.back ((formT_elim _ _ _ _ _ _ _).trans (nockOK31_beta _ _ _ _ _ _)) (force_exit ((ih1 hes).2 hc))

-- ---------------------------------------------------------------------------
-- The theorems of PLAN.md §2.4
-- ---------------------------------------------------------------------------

/-- **`embed_crash`**: a Nock crash is a reduction to `Err`, on any
    encoding of the subject. -/
theorem embed_crash {s f : Noun} {es : Term} (h : NockEval s f .exit) (hes : Enc s es) :
    WSteps (nockToSki f ⬝ es) errT :=
  (embed_both h hes).1

/-- **`embed_value`**: a Nock value is a reduction to an encoding of it,
    on any encoding of the subject (M3: no `Err` disjunct). -/
theorem embed_value {s f p : Noun} {es : Term} (h : NockEval s f (.val p)) (hes : Enc s es) :
    ∃ ep, Enc p ep ∧ WSteps (nockToSki f ⬝ es) ep :=
  (embed_both h hes).1

/-- **`nockI_crash`**: the interpreter crashes where Nock does, on any
    encodings of the subject and the formula. -/
theorem nockI_crash {s f : Noun} {es ef : Term} (h : NockEval s f .exit) (hes : Enc s es) (hef : Enc f ef) :
    WSteps (nockIT ⬝ es ⬝ ef) errT :=
  (WSteps.left _ (WSteps.left _ nockIT_fix)).trans ((embed_both h hes).2 hef)

/-- **`nockI_value`**: the interpreter computes an encoding of Nock's
    value, on any encodings of the subject and the formula. -/
theorem nockI_value {s f p : Noun} {es ef : Term} (h : NockEval s f (.val p)) (hes : Enc s es) (hef : Enc f ef) :
    ∃ ep, Enc p ep ∧ WSteps (nockIT ⬝ es ⬝ ef) ep := by
  obtain ⟨ep, hp, he⟩ := (embed_both h hes).2 hef
  exact ⟨ep, hp, (WSteps.left _ (WSteps.left _ nockIT_fix)).trans he⟩

/-- On the program `compiled f s` (the subject as the runtime's literal). -/
theorem compiled_crash {s f : Noun} (h : NockEval s f .exit) : WSteps (compiled f s) errT :=
  embed_crash h (enc_encLit s)

theorem compiled_value {s f p : Noun} (h : NockEval s f (.val p)) :
    ∃ ep, Enc p ep ∧ WSteps (compiled f s) ep :=
  embed_value h (enc_encLit s)

/-- On the code-free subject `encNoun s`, the hidden subject of the
    statement path. -/
theorem embed_crash_encNoun {s f : Noun} (h : NockEval s f .exit) :
    WSteps (nockToSki f ⬝ encNoun s) errT :=
  embed_crash h (enc_encNoun s)

theorem embed_value_encNoun {s f p : Noun} (h : NockEval s f (.val p)) :
    ∃ ep, Enc p ep ∧ WSteps (nockToSki f ⬝ encNoun s) ep :=
  embed_value h (enc_encNoun s)

/-- The interpreted program: the formula as code-free data beside the
    subject, run by `[2 [0 2] [0 3]]` (the second gate of `normcheck`). -/
theorem interpreted_value {s f p : Noun} (h : NockEval s f (.val p)) :
    ∃ ep, Enc p ep ∧ WSteps (nockToSki (.cell (.atom 2) (.cell (.cell (.atom 0) (.atom 2))
      (.cell (.atom 0) (.atom 3)))) ⬝ encNoun (.cell s f)) ep :=
  embed_value (NockEval.op2 (NockEval.op0 (fasO_head s f)) (NockEval.op0 (fasO_tail s f)) h) (enc_encNoun _)

end Nock2Ski
