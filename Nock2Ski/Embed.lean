import Nock2Ski.Enc

open Term

/-!
# The simulation: `NockEval` carried to weak reduction

Milestone M2 of `PLAN.md`, §2.4.  For every lean-nock derivation
`NockEval s f o` and every encoding `es` of the subject (`Enc s es`,
`Nock2Ski/Enc.lean`), the compiled program `nockToSki f ⬝ es` weakly
reduces as the outcome says:

- `embed_crash`: `o = .exit` gives `nockToSki f ⬝ es ↠ Err`.
- `embed_value`: `o = .val p` gives `nockToSki f ⬝ es ↠ ep` for some
  encoding `ep` of `p`, **or** `nockToSki f ⬝ es ↠ Err`.

The second disjunct is exact, not a weakness of the proof.  Opcodes 2 and
9 run a formula that is a *value*: in Nock any noun, in the runtime a term
that carries code only if it came from a literal (`encLit`) or was
projected out of one.  A formula assembled by autocons or edit, or taken
from a code-free subject, reaches `app` as a plain `Cell`, and M1's `app`
(`app_noun`) crashes there; the Python runtime falls back to the
interpreter `nockI`, which lean-ski's front end cannot yet pin (PLAN.md,
Status).  So the SKI term never produces a wrong value and never diverges
where Nock produces a value; it crashes where Nock crashes, and it crashes
also at an application of a code-free formula.  `embed_value_noCrash` is
the strong form under the hypothesis that the run does not crash, and the
Hoon-shaped fragment of §2.3, where every formula reaching 2 or 9 carries
code, is where that hypothesis holds by construction (M3's
`fragment_static`).

## The proof

`Sim o e` is the conclusion for one outcome; `embed` is one induction on
`NockEval` over `Sim`, and each case is: the **step lemma** of the opcode
(`step_op4 : nockToSki [4 b] ⬝ s ↠ inc (B ⬝ s)`, β for the `λs` by
`abs_beta_close` and `simp` on the closing), then `force_sim` for every
operand Nock evaluates first (a value goes to the continuation, a crash
propagates, `force_enc`/`force_err`), the β of the helper combinator
(`consK_beta`, …), the primitive's spec over `Enc`, and the induction
hypothesis on the remaining operand with the new subject.  Opcode 0 and 9
use `pick_enc` along `axisPath`, with `fasO_axisPath` to read lean-nock's
`fasO`; opcode 10 uses `editT_enc`, the walk of compile.py's `edit`, with
`haxO_axisPath`.
-/

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
  simp only [_root_.appT, OTerm.close, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem appK_beta (e x : Term) :
    ∃ kx, WSteps (appK ⬝ e ⬝ x) (forceT ⬝ e ⬝ kx) ∧ ∀ g, WSteps (kx ⬝ g) (appT ⬝ g ⬝ x) := by
  have h := absN_beta_close [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ absN [2] (appT.toO ⬝ₒ v2 ⬝ₒ v1))
    (fun _ => K) [e, x] rfl
  simp only [_root_.appT, OTerm.close, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  refine ⟨_, h, fun g => ?_⟩
  have h2 := abs_beta_close 2 (appT.toO ⬝ₒ v2 ⬝ₒ v1) (updC (updC (fun _ => K) 0 e) 1 x) g
  simp only [OTerm.close, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h2
  exact h2

theorem eqK_beta (e x : Term) : WSteps (eqK ⬝ e ⬝ x) (forceT ⬝ e ⬝ (eqT ⬝ x)) := by
  have h := absN_beta_close [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ (eqT.toO ⬝ₒ v1)) (fun _ => K) [e, x] rfl
  simp only [_root_.appT, OTerm.close, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem pushK_beta (c s x : Term) : WSteps (pushK ⬝ c ⬝ s ⬝ x) (c ⬝ (CellC ⬝ x ⬝ s)) := by
  have h := absN_beta_close [0, 1, 2] (v0 ⬝ₒ (CellC.toO ⬝ₒ v2 ⬝ₒ v1)) (fun _ => K) [c, s, x] rfl
  simp only [_root_.appT, OTerm.close, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  exact h

theorem pullK_zero (core : Term) : WSteps (pullK (.atom 0) ⬝ core) (appT ⬝ errT ⬝ core) := by
  have h := abs_beta_close 0 (appT.toO ⬝ₒ axisO 0 v0 ⬝ₒ v0) (fun _ => K) core
  simp only [axisO, OTerm.close, close_toO, updC, ↓reduceIte] at h
  exact h

theorem pullK_succ (k : Nat) (core : Term) :
    WSteps (pullK (.atom (k + 1)) ⬝ core) (appT ⬝ pickT core (axisPath (k + 1)) ⬝ core) := by
  have h := abs_beta_close 0 (appT.toO ⬝ₒ axisO (k + 1) v0 ⬝ₒ v0) (fun _ => K) core
  simp only [axisO, close_pickO, OTerm.close, close_toO, updC, ↓reduceIte] at h
  exact h

theorem editK_beta (b : Noun) (c t : Term) :
    ∃ kv, WSteps (editK b ⬝ c ⬝ t) (forceT ⬝ c ⬝ kv) ∧ ∀ v, WSteps (kv ⬝ v) (editAx b ⬝ v ⬝ t) := by
  have h := absN_beta_close [0, 1] (forceT.toO ⬝ₒ v0 ⬝ₒ absN [2] ((editAx b).toO ⬝ₒ v2 ⬝ₒ v1))
    (fun _ => K) [c, t] rfl
  simp only [_root_.appT, OTerm.close, close_toO, overrideC, updC, Nat.reduceEqDiff, ↓reduceIte] at h
  refine ⟨_, h, fun v => ?_⟩
  have h2 := abs_beta_close 2 ((editAx b).toO ⬝ₒ v2 ⬝ₒ v1) (updC (updC (fun _ => K) 0 c) 1 t) v
  simp only [OTerm.close, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h2
  exact h2

-- ---------------------------------------------------------------------------
-- The edit walk: compile.py's `edit` along a path, over `Enc`
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
  simp only [_root_.appT, OTerm.close, close_toO, overrideC, updC, ↓reduceIte] at h
  refine ⟨_, h, fun hd => ?_⟩
  have h2 := abs_beta_close 2
    (forceT.toO ⬝ₒ (tlT.toO ⬝ₒ v1) ⬝ₒ absN [3]
      (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v2) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v4 ⬝ₒ v3)))
    (updC (updC (fun _ => K) 0 v) 1 cur) hd
  simp only [OTerm.close, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h2
  refine ⟨_, h2, fun tl => ?_⟩
  have h3 := abs_beta_close 3
    (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v2) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v4 ⬝ₒ v3))
    (updC (updC (updC (fun _ => K) 0 v) 1 cur) 2 hd) tl
  simp only [OTerm.close, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h3
  refine ⟨_, h3, fun i => ?_⟩
  have h4 := abs_beta_close 4 (CellC.toO ⬝ₒ v4 ⬝ₒ v3)
    (updC (updC (updC (updC (fun _ => K) 0 v) 1 cur) 2 hd) 3 tl) i
  simp only [OTerm.close, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h4
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
  simp only [_root_.appT, OTerm.close, close_toO, overrideC, updC, ↓reduceIte] at h
  refine ⟨_, h, fun hd => ?_⟩
  have h2 := abs_beta_close 2
    (forceT.toO ⬝ₒ (tlT.toO ⬝ₒ v1) ⬝ₒ absN [3]
      (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v3) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v2 ⬝ₒ v4)))
    (updC (updC (fun _ => K) 0 v) 1 cur) hd
  simp only [OTerm.close, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h2
  refine ⟨_, h2, fun tl => ?_⟩
  have h3 := abs_beta_close 3
    (forceT.toO ⬝ₒ ((editT bs).toO ⬝ₒ v0 ⬝ₒ v3) ⬝ₒ absN [4] (CellC.toO ⬝ₒ v2 ⬝ₒ v4))
    (updC (updC (updC (fun _ => K) 0 v) 1 cur) 2 hd) tl
  simp only [OTerm.close, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h3
  refine ⟨_, h3, fun i => ?_⟩
  have h4 := abs_beta_close 4 (CellC.toO ⬝ₒ v2 ⬝ₒ v4)
    (updC (updC (updC (updC (fun _ => K) 0 v) 1 cur) 2 hd) 3 tl) i
  simp only [OTerm.close, close_toO, updC, Nat.reduceEqDiff, ↓reduceIte] at h4
  exact h4

/-- `forceT ⬝ t ⬝ k` when `t` meets a noun: the continuation gets an
    encoding, or the crash propagates. -/
theorem force_meets {o : Option Noun} {t k : Term} {P : Term → Prop}
    (ht : Meets o t) (hk : ∀ r e, o = some r → Enc r e → P (k ⬝ e)) (herr : P errT)
    (hback : ∀ {a b}, WSteps a b → P b → P a) : P (forceT ⬝ t ⬝ k) := by
  cases o with
  | none => exact hback ((WSteps.left _ (WSteps.right _ ht)).trans (force_err k)) herr
  | some r =>
    obtain ⟨e, he, hte⟩ := ht
    exact hback ((WSteps.left _ (WSteps.right _ hte)).trans (force_enc he k)) (hk r e rfl he)

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
             simp only [axisO, close_pickO, OTerm.close, close_toO, at0, updC, ↓reduceIte]
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

/-- The conclusion for one outcome: a crash reduces to `Err`; a value
    reduces to an encoding of it, or to `Err` (an application of a
    code-free formula, see the module comment). -/
def Sim : Outcome → Term → Prop
  | .val p, e => (∃ ep, Enc p ep ∧ WSteps e ep) ∨ WSteps e errT
  | .exit, e => WSteps e errT

theorem Sim.back {o : Outcome} {e e' : Term} (h : WSteps e e') (hs : Sim o e') : Sim o e := by
  cases o with
  | exit => exact h.trans hs
  | val p =>
    rcases hs with ⟨ep, hp, he⟩ | herr
    · exact .inl ⟨ep, hp, h.trans he⟩
    · exact .inr (h.trans herr)

theorem Sim.err {o : Outcome} {e : Term} (h : WSteps e errT) : Sim o e := by
  cases o with
  | exit => exact h
  | val _ => exact .inr h

theorem Sim.val {p : Noun} {e ep : Term} (hp : Enc p ep) (h : WSteps e ep) : Sim (.val p) e :=
  .inl ⟨ep, hp, h⟩

/-- `force` of an operand that simulates a value: the continuation runs on
    an encoding of it, or the crash propagates. -/
theorem force_sim {r : Noun} {t k : Term} {o : Outcome} (ht : Sim (.val r) t)
    (hk : ∀ e, Enc r e → Sim o (k ⬝ e)) : Sim o (forceT ⬝ t ⬝ k) := by
  rcases ht with ⟨e, he, hte⟩ | herr
  · exact Sim.back ((WSteps.left _ (WSteps.right _ hte)).trans (force_enc he k)) (hk e he)
  · exact Sim.err ((WSteps.left _ (WSteps.right _ herr)).trans (force_err k))

/-- `force` of an operand that crashes. -/
theorem force_err_sim {t k : Term} {o : Outcome} (ht : WSteps t errT) : Sim o (forceT ⬝ t ⬝ k) :=
  Sim.err ((WSteps.left _ (WSteps.right _ ht)).trans (force_err k))

/-- `app` of an encoded formula on an encoded subject simulates the
    evaluation when the formula carries code, and crashes otherwise. -/
theorem app_sim {r2 r1 : Noun} {e2 e1 : Term} {o : Outcome} (h2 : Enc r2 e2)
    (ih : ∀ {es}, Enc r1 es → Sim o (nockToSki r2 ⬝ es)) (h1 : Enc r1 e1) :
    Sim o (appT ⬝ e2 ⬝ e1) := by
  cases r2 with
  | atom n => exact Sim.err (app_enc_atom h2)
  | cell h t =>
    rcases app_enc h2 (x := e1) with hf | herr
    · exact Sim.back hf (ih h1)
    · exact Sim.err herr

/-- **The simulation.**  Every lean-nock derivation is carried to weak
    reduction of the compiled program on any encoding of the subject. -/
theorem embed {s f : Noun} {o : Outcome} (h : NockEval s f o) :
    ∀ {es : Term}, Enc s es → Sim o (nockToSki f ⬝ es) := by
  induction h with
  | crash_malformed hm =>
    intro es _
    exact Sim.err (step_malformed hm es)
  -- autocons
  | autocons _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_autocons _ _ _ es) (force_sim (ih1 hes) fun e1 he1 => ?_)
    refine Sim.back (consK_beta _ _) (force_sim (ih2 hes) fun e2 he2 => ?_)
    exact Sim.val (.cell he1 he2) (CellC_red e1 e2)
  | autocons_crashL _ ih1 =>
    intro es hes
    exact Sim.back (step_autocons _ _ _ es) (force_err_sim (ih1 hes))
  | autocons_crashR _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_autocons _ _ _ es) (force_sim (ih1 hes) fun e1 _ => ?_)
    exact Sim.back (consK_beta _ _) (force_err_sim (ih2 hes))
  -- 0
  | @op0 a fol r hfas =>
    intro es hes
    cases fol with
    | cell p q => rw [fasO_cell] at hfas; cases hfas
    | atom n =>
      cases n with
      | zero => rw [fasO_zero] at hfas; cases hfas
      | succ k =>
        rw [fasO_axisPath _ _ (by omega)] at hfas
        obtain ⟨er, her, hp⟩ := pick_enc _ r hfas hes (.refl es)
        exact Sim.val her ((step_op0 k es).trans hp)
  | @op0_crash a fol hfas =>
    intro es hes
    cases fol with
    | cell p q => exact Sim.err (step_op0_cell p q es)
    | atom n =>
      cases n with
      | zero => exact Sim.err (step_op0_zero es)
      | succ k =>
        rw [fasO_axisPath _ _ (by omega)] at hfas
        exact Sim.err ((step_op0 k es).trans (pick_enc_none _ hfas hes (.refl es)))
  -- 1
  | op1 =>
    intro es _
    exact Sim.val (enc_encLit _) (step_op1 _ es)
  -- 2
  | op2 _ _ _ ih1 ih2 ih3 =>
    intro es hes
    refine Sim.back (step_op2 _ _ es) (force_sim (ih1 hes) fun e1 he1 => ?_)
    obtain ⟨kx, hb, hkx⟩ := appK_beta (nockToSki _ ⬝ es) e1
    refine Sim.back hb (force_sim (ih2 hes) fun e2 he2 => Sim.back (hkx e2) ?_)
    exact app_sim he2 ih3 he1
  | op2_crashL _ ih1 =>
    intro es hes
    exact Sim.back (step_op2 _ _ es) (force_err_sim (ih1 hes))
  | op2_crashR _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_op2 _ _ es) (force_sim (ih1 hes) fun e1 _ => ?_)
    obtain ⟨kx, hb, _⟩ := appK_beta (nockToSki _ ⬝ es) e1
    exact Sim.back hb (force_err_sim (ih2 hes))
  -- 3
  | op3 _ ih =>
    intro es hes
    refine Sim.back (step_op3 _ es) ?_
    rcases ih hes with ⟨e, he, hB⟩ | herr
    · exact Sim.val (enc_encNoun _) ((WSteps.right _ hB).trans (cel_enc he))
    · exact Sim.err ((WSteps.right _ herr).trans cel_err)
  | op3_crash _ ih =>
    intro es hes
    exact Sim.back (step_op3 _ es) (Sim.err ((WSteps.right _ (ih hes)).trans cel_err))
  -- 4
  | @op4 a fol r v _ hl ih =>
    intro es hes
    refine Sim.back (step_op4 _ es) ?_
    rcases ih hes with ⟨e, he, hB⟩ | herr
    · cases r with
      | atom n =>
        rw [lusO_atom] at hl
        cases hl
        exact Sim.val (enc_encNoun _) ((WSteps.right _ hB).trans (inc_enc_atom he))
      | cell _ _ => rw [lusO_cell] at hl; cases hl
    · exact Sim.err ((WSteps.right _ herr).trans inc_err)
  | @op4_cell a fol r _ hl ih =>
    intro es hes
    refine Sim.back (step_op4 _ es) ?_
    rcases ih hes with ⟨e, he, hB⟩ | herr
    · cases r with
      | atom n => rw [lusO_atom] at hl; cases hl
      | cell _ _ => exact Sim.err ((WSteps.right _ hB).trans (inc_enc_cell he))
    · exact Sim.err ((WSteps.right _ herr).trans inc_err)
  | op4_crash _ ih =>
    intro es hes
    exact Sim.back (step_op4 _ es) (Sim.err ((WSteps.right _ (ih hes)).trans inc_err))
  -- 5
  | op5 _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_op5 _ _ es) (force_sim (ih1 hes) fun e1 he1 => ?_)
    refine Sim.back (eqK_beta _ _) (force_sim (ih2 hes) fun e2 he2 => ?_)
    exact Sim.val (enc_encNoun _) (eq_enc he1 he2)
  | op5_crashL _ ih1 =>
    intro es hes
    exact Sim.back (step_op5 _ _ es) (force_err_sim (ih1 hes))
  | op5_crashR _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_op5 _ _ es) (force_sim (ih1 hes) fun e1 _ => ?_)
    exact Sim.back (eqK_beta _ _) (force_err_sim (ih2 hes))
  -- 6
  | op6_then _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_op6 _ _ _ es) ?_
    rcases ih1 hes with ⟨e, he, hB⟩ | herr
    · exact Sim.back ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans
        (ifn_enc_zero he _ _)) (ih2 hes)
    · exact Sim.err ((WSteps.left _ (WSteps.left _ (WSteps.right _ herr))).trans (ifn_err _ _))
  | op6_else _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_op6 _ _ _ es) ?_
    rcases ih1 hes with ⟨e, he, hB⟩ | herr
    · exact Sim.back ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans
        (ifn_enc_one he _ _)) (ih2 hes)
    · exact Sim.err ((WSteps.left _ (WSteps.left _ (WSteps.right _ herr))).trans (ifn_err _ _))
  | op6_nonloob _ h0 h1 ih1 =>
    intro es hes
    refine Sim.back (step_op6 _ _ _ es) ?_
    rcases ih1 hes with ⟨e, he, hB⟩ | herr
    · exact Sim.err ((WSteps.left _ (WSteps.left _ (WSteps.right _ hB))).trans
        (ifn_enc_crash he h0 h1 _ _))
    · exact Sim.err ((WSteps.left _ (WSteps.left _ (WSteps.right _ herr))).trans (ifn_err _ _))
  | op6_crash _ ih1 =>
    intro es hes
    exact Sim.back (step_op6 _ _ _ es)
      (Sim.err ((WSteps.left _ (WSteps.left _ (WSteps.right _ (ih1 hes)))).trans (ifn_err _ _)))
  -- 7
  | op7 _ _ ih1 ih2 =>
    intro es hes
    exact Sim.back (step_op7 _ _ es) (force_sim (ih1 hes) fun e1 he1 => ih2 he1)
  | op7_crash _ ih1 =>
    intro es hes
    exact Sim.back (step_op7 _ _ es) (force_err_sim (ih1 hes))
  -- 8
  | op8 _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_op8 _ _ es) (force_sim (ih1 hes) fun e1 he1 => ?_)
    exact Sim.back ((pushK_beta _ _ _).trans (WSteps.right _ (CellC_red e1 es))) (ih2 (.cell he1 hes))
  | op8_crash _ ih1 =>
    intro es hes
    exact Sim.back (step_op8 _ _ es) (force_err_sim (ih1 hes))
  -- 9
  | @op9 a b c core arm o _ hfas _ ih1 ih3 =>
    intro es hes
    refine Sim.back (step_op9 _ _ es) (force_sim (ih1 hes) fun ec hec => ?_)
    cases b with
    | cell p q => rw [fasO_cell] at hfas; cases hfas
    | atom n =>
      cases n with
      | zero => rw [fasO_zero] at hfas; cases hfas
      | succ k =>
        rw [fasO_axisPath _ _ (by omega)] at hfas
        obtain ⟨ea, hea, hp⟩ := pick_enc _ arm hfas hec (.refl ec)
        refine Sim.back ((pullK_succ k ec).trans (WSteps.left _ (WSteps.right _ hp))) ?_
        exact app_sim hea ih3 hec
  | @op9_badaxis a b c core _ hfas ih1 =>
    intro es hes
    refine Sim.back (step_op9 _ _ es) (force_sim (ih1 hes) fun ec hec => ?_)
    cases b with
    | cell p q => exact Sim.err (.single (.K _ _))
    | atom n =>
      cases n with
      | zero => exact Sim.err ((pullK_zero ec).trans (app_err ec))
      | succ k =>
        rw [fasO_axisPath _ _ (by omega)] at hfas
        exact Sim.err ((pullK_succ k ec).trans
          ((WSteps.left _ (WSteps.right _ (pick_enc_none _ hfas hec (.refl ec)))).trans (app_err ec)))
  | op9_crash _ ih1 =>
    intro es hes
    exact Sim.back (step_op9 _ _ es) (force_err_sim (ih1 hes))
  -- 10
  | @op10 a b c d r1 r2 v _ _ hhax ihd ihc =>
    intro es hes
    refine Sim.back (step_op10 _ _ _ es) (force_sim (ihd hes) fun e2 he2 => ?_)
    obtain ⟨kv, hb, hkv⟩ := editK_beta b (nockToSki c ⬝ es) e2
    refine Sim.back hb (force_sim (ihc hes) fun e1 he1 => Sim.back (hkv e1) ?_)
    have hm := editAx_enc (b := b) he1 he2
    rw [hhax] at hm
    obtain ⟨ev, hv, hev⟩ := hm
    exact Sim.val hv hev
  | @op10_badaxis a b c d r1 r2 _ _ hhax ihd ihc =>
    intro es hes
    refine Sim.back (step_op10 _ _ _ es) (force_sim (ihd hes) fun e2 he2 => ?_)
    obtain ⟨kv, hb, hkv⟩ := editK_beta b (nockToSki c ⬝ es) e2
    refine Sim.back hb (force_sim (ihc hes) fun e1 he1 => Sim.back (hkv e1) ?_)
    have hm := editAx_enc (b := b) he1 he2
    rw [hhax] at hm
    exact Sim.err hm
  | op10_crashTree _ ihd =>
    intro es hes
    exact Sim.back (step_op10 _ _ _ es) (force_err_sim (ihd hes))
  | op10_crashPatch _ _ ihd ihc =>
    intro es hes
    refine Sim.back (step_op10 _ _ _ es) (force_sim (ihd hes) fun e2 _ => ?_)
    obtain ⟨kv, hb, _⟩ := editK_beta _ (nockToSki _ ⬝ es) e2
    exact Sim.back hb (force_err_sim (ihc hes))
  -- 11
  | op11_static _ ih =>
    intro es hes
    rw [step_op11_static]
    exact ih hes
  | op11_dynamic _ _ ih1 ih2 =>
    intro es hes
    refine Sim.back (step_op11_dynamic _ _ _ es) (force_sim (ih1 hes) fun e1 _ => ?_)
    exact Sim.back (.single (.K _ _)) (ih2 hes)
  | op11_dyn_crash _ ih1 =>
    intro es hes
    exact Sim.back (step_op11_dynamic _ _ _ es) (force_err_sim (ih1 hes))

-- ---------------------------------------------------------------------------
-- The theorems of PLAN.md §2.4
-- ---------------------------------------------------------------------------

/-- **`embed_crash`**: a Nock crash is a reduction to `Err`, on any
    encoding of the subject. -/
theorem embed_crash {s f : Noun} {es : Term} (h : NockEval s f .exit) (hes : Enc s es) :
    WSteps (nockToSki f ⬝ es) errT :=
  embed h hes

/-- **`embed_value`**: a Nock value is a reduction to an encoding of it,
    or to `Err` at an application of a code-free formula. -/
theorem embed_value {s f p : Noun} {es : Term} (h : NockEval s f (.val p)) (hes : Enc s es) :
    (∃ ep, Enc p ep ∧ WSteps (nockToSki f ⬝ es) ep) ∨ WSteps (nockToSki f ⬝ es) errT :=
  embed h hes

/-- The strong form: a run that does not crash computes the value. -/
theorem embed_value_noCrash {s f p : Noun} {es : Term} (h : NockEval s f (.val p)) (hes : Enc s es)
    (hnc : ¬ WSteps (nockToSki f ⬝ es) errT) : ∃ ep, Enc p ep ∧ WSteps (nockToSki f ⬝ es) ep := by
  rcases embed_value h hes with hv | herr
  · exact hv
  · exact absurd herr hnc

/-- On the program `compiled f s` (the subject as the runtime's literal). -/
theorem compiled_crash {s f : Noun} (h : NockEval s f .exit) : WSteps (compiled f s) errT :=
  embed_crash h (enc_encLit s)

theorem compiled_value {s f p : Noun} (h : NockEval s f (.val p)) :
    (∃ ep, Enc p ep ∧ WSteps (compiled f s) ep) ∨ WSteps (compiled f s) errT :=
  embed_value h (enc_encLit s)

/-- On the code-free subject `encNoun s`, the hidden subject of the
    statement path. -/
theorem embed_crash_encNoun {s f : Noun} (h : NockEval s f .exit) :
    WSteps (nockToSki f ⬝ encNoun s) errT :=
  embed_crash h (enc_encNoun s)

theorem embed_value_encNoun {s f p : Noun} (h : NockEval s f (.val p)) :
    (∃ ep, Enc p ep ∧ WSteps (nockToSki f ⬝ encNoun s) ep) ∨ WSteps (nockToSki f ⬝ encNoun s) errT :=
  embed_value h (enc_encNoun s)

end Nock2Ski
