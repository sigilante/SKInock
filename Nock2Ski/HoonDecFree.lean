import Nock2Ski.HoonDec

open Nock (Noun NockEval Outcome tisN)
open Nock.Noun
open Term

/-!
# Hoon's `++dec` on real gate cores: any encoding, and any battery and context

`hoon_dec_transport` (`Nock2Ski/HoonDec.lean`) is stated over `encNoun`
inputs, which never contain a `Form`.  A real compiled gate core `[bat [sam
ctx]]` carries code: its battery and its context were pushed by `[1 …]`, and
the runtime's literals are `Form`s (`encLit`).  This module states the jet on
those inputs.

- **(a) any encoding**: `hoon_dec_enc : Enc s es → HoonDecDom s →
  jetT hoonDecBodyF ⬝ es ↠ encOut (hoonDecC s)`, from `embed_value` and
  `embed_crash` (which hold for every encoding `Enc s es`, `Form`s
  included), then `toCell_enc` / `toCell_err`.
- **(b) any terms at axes 2 and 7, either cell a `Form`**: for arbitrary
  closed terms `B` and `C`, no `Enc` hypothesis, on a subject `s` with
  `CellLike s B X` and `CellLike X ⟨m⟩ C` (each cell literally `cellT h t`
  or `formT h t k` with any code `k`, never read), the sample the canonical
  atom `⟨m⟩ = encNoun (atom m)`: `hoon_dec_free_cl` (`m = n + 1` gives
  `⟨n⟩`) and `hoon_dec_free_cl_zero` (`m = 0` gives `Err`);
  `hoon_dec_free`, `hoon_dec_free_form`, `hoon_dec_free_zero` are the
  `cellT`/`formT` instances.  A cell sample is excluded: there the arm
  diverges (`hoon_dec_off_domain_term`).
- **The `Err` shapes**, any bits: `hoon_dec_err_atom b` (the core `atomT b`)
  and `hoon_dec_err_noSample b` (a cell-like `[B (atomT b)]`), for **any**
  bit term `b`, canonical or not: the arm only cases on the constructor
  (`hd_atomT`, `tl_atomT`, from the open runs `hd_atom_run`, `tl_atom_run`).
  The sample-`0` crash needs the canonical `⟨0⟩`: `eqT` compares bit lists,
  and a non-canonical zero is unequal to the literal `0`.

**Why (b) holds.**  The proof runs the compiled arm step by step, with `B`
and `C` universally quantified closed terms (no kernel run: each step is a
lemma of `Embed.lean` or `Enc.lean` stated for arbitrary fields).  Every operation that inspects the subject is one of
`hdT`, `tlT` (axis pulls), `forceT` (to weak head normal form) and the
edit walk `editT`, and each of these looks only at the outer constructor of
the cell it is given (`hd_cellT`, `tl_cellT`, `force_cellT`, for any
fields).  The places the arm reaches are:

- the guard `[5 [1 0] [0 6]]`: axis 6, the sample, compared with `0`;
- `[8 [1 0] [8 [1 loop] [9 2 0 1]]]`: the counter `0` and the loop
  battery `loop` (a `Form`, `loopE`) are pushed, giving the loop core
  `decCore i S = cellT loopE (cellT ⟨i⟩ S)` with the whole subject `S`
  **copied as a field**, then `loop` is pulled from axis 2 and run on the
  core (`dec_pull`, by `app_form`);
- in the loop, `[5 [0 30] [4 0 6]]` reads axis 30 of the core (the sample
  `⟨m⟩`, through the copied `S`: `tl`, `tl`, `tl`, `hd`) and axis 6 (the
  counter); `[0 6]` returns the counter; `[10 [6 [4 0 6]] [0 1]]` rebuilds
  the core at axis 6 (`dec_edit`): the walk forces the battery `loopE`,
  the cell `cellT ⟨i⟩ S`, the counter, and **`S` itself to its outer
  constructor**, which is `cellT B (cellT ⟨m⟩ C)` already.

So `B` and `C` ride along inside `S` and are never applied, projected into
or forced.  The equality `eqT` and the increment `incT` only ever see the
canonical atoms `⟨m⟩`, `⟨i⟩`, `⟨i + 1⟩`.  No step forces `B` or `C`.

**The fire check** (`hoonDecFire? : Term → Option Term`): `some u` to
fire with output `u`, `none` to decline.  It fires `Err` on the `Err`
shapes (`HoonDecErrFires`: literally `atomT b`, or a literal cell-like
`[B (atomT b)]`), and otherwise on a literal cell-like `[B [⟨m⟩ C]]`, `⟨m⟩`
canonical, `m < 2^32` (`HoonDecFires`), with `encOut (hoonDecOutN m)`:
`⟨m - 1⟩` for `m ≥ 1`, `Err` at `0`.  `hoon_dec_fire_sound`: whenever it
fires, `jetT hoonDecBodyF ⬝ t ↠ u`.  `hoonDecSample?_cl`: the sample check
accepts every cell-like `[B [⟨m⟩ C]]`, whatever `B`, `C` and the codes are.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- (a) Any encoding of the subject
-- ---------------------------------------------------------------------------

/-- `jet_step` over any encoding of the subject, `Form`s included. -/
theorem jet_step_enc {f s : Noun} {o : Outcome} {es : Term} (h : NockEval s f o) (hes : Enc s es) :
    WSteps (jetT f ⬝ es) (encOut o) := by
  refine (jetT_red f _).trans ?_
  cases o with
  | val p =>
    obtain ⟨ep, hp, he⟩ := embed_value h hes
    exact (WSteps.right _ he).trans (toCell_enc hp)
  | exit => exact (WSteps.right _ (embed_crash h hes)).trans toCell_err

/-- **(a)** The Hoon `++dec` jet on any encoding of a domain subject: a
    compiled core whose battery and context are `Form`s carrying code. -/
theorem hoon_dec_enc {s : Noun} {es : Term} (hes : Enc s es) (hs : HoonDecDom s) :
    WSteps (jetT hoonDecBodyF ⬝ es) (encOut (hoonDecC s)) :=
  jet_step_enc (hoon_dec_leaf s hs) hes

-- ---------------------------------------------------------------------------
-- (b) The arm in parts
-- ---------------------------------------------------------------------------

/-- The canonical atom `⟨k⟩`. -/
abbrev aT (k : Nat) : Term := encNoun (.atom k)

/-- The loop battery the arm pushes: `[6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1]`. -/
def hoonDecLoopF : Noun := n! "[6 [5 [0 30] 4 0 6] [0 6] 9 2 10 [6 4 0 6] 0 1]"

/-- The arm: guard, then push the counter and the loop battery, then pull. -/
theorem hoonDecBodyF_split : hoonDecBodyF =
    cell (atom 6) (cell (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 6))))
      (cell (cell (atom 0) (atom 0))
        (cell (atom 8) (cell (cell (atom 1) (atom 0))
          (cell (atom 8) (cell (cell (atom 1) hoonDecLoopF)
            (cell (atom 9) (cell (atom 2) (cell (atom 0) (atom 1)))))))))) := rfl

/-- The loop: test `sam = ctr + 1`, return `ctr`, or edit and recurse. -/
theorem hoonDecLoopF_split : hoonDecLoopF =
    cell (atom 6) (cell
      (cell (atom 5) (cell (cell (atom 0) (atom 30)) (cell (atom 4) (cell (atom 0) (atom 6)))))
      (cell (cell (atom 0) (atom 6))
        (cell (atom 9) (cell (atom 2)
          (cell (atom 10) (cell (cell (atom 6) (cell (atom 4) (cell (atom 0) (atom 6))))
            (cell (atom 0) (atom 1)))))))) := rfl

/-- The loop battery as the runtime pushes it: a `Form` with its code. -/
def loopE : Term := encLit hoonDecLoopF

theorem loopE_enc : Enc hoonDecLoopF loopE := enc_encLit _

theorem loopE_form : ∃ eh et, loopE = formT eh et (nockToSki hoonDecLoopF) :=
  ⟨_, _, by unfold loopE; rw [hoonDecLoopF_split, encLit, if_pos (by decide)]⟩

/-- The loop core `[loop [ctr S]]`, `S` the whole subject copied. -/
def decCore (i : Nat) (s : Term) : Term := cellT loopE (cellT (aT i) s)

-- ---------------------------------------------------------------------------
-- Axes and the steps the arm takes
-- ---------------------------------------------------------------------------

theorem axisPath_1 : axisPath (0 + 1) = [] := by simp [axisPath_one]
theorem axisPath_2 : axisPath (1 + 1) = [false] := by
  simp [axisPath_rec, axisPath_one]
theorem axisPath_6 : axisPath (5 + 1) = [true, false] := by
  simp [axisPath_rec, axisPath_one]
theorem axisPath_30 : axisPath (29 + 1) = [true, true, true, false] := by
  simp [axisPath_rec, axisPath_one]

theorem op0_1 (s : Term) : WSteps (nockToSki (cell (atom 0) (atom 1)) ⬝ s) s := by
  have h := step_op0 0 s
  rw [axisPath_1] at h
  exact h

theorem op0_6 (s : Term) : WSteps (nockToSki (cell (atom 0) (atom 6)) ⬝ s) (hdT ⬝ (tlT ⬝ s)) := by
  have h := step_op0 5 s
  rw [axisPath_6] at h
  exact h

theorem op0_30 (s : Term) :
    WSteps (nockToSki (cell (atom 0) (atom 30)) ⬝ s) (hdT ⬝ (tlT ⬝ (tlT ⬝ (tlT ⬝ s)))) := by
  have h := step_op0 29 s
  rw [axisPath_30] at h
  exact h

theorem pull2 (core : Term) : WSteps (pullK (atom 2) ⬝ core) (appT ⬝ (hdT ⬝ core) ⬝ core) := by
  have h := pullK_succ 1 core
  rw [axisPath_2] at h
  exact h

theorem app_loopE (x : Term) : WSteps (appT ⬝ loopE ⬝ x) (nockToSki hoonDecLoopF ⬝ x) := by
  obtain ⟨eh, et, he⟩ := loopE_form
  rw [he]
  exact app_form _ _ _ _

-- ---------------------------------------------------------------------------
-- Cell-like terms: a `Cell` or a `Form` with any code
-- ---------------------------------------------------------------------------

/-- `x` is the cell `[h t]` as the runtime may encode it: `cellT h t`, or
    `formT h t k` with any code `k` (a formula-shaped cell pushed by `[1 …]`;
    `[n ctx]` with `n ≤ 11` reads as an opcode).  `k` is never read. -/
def CellLike (x h t : Term) : Prop := x = cellT h t ∨ ∃ k, x = formT h t k

theorem CellLike.cell (h t : Term) : CellLike (cellT h t) h t := .inl rfl
theorem CellLike.form (h t k : Term) : CellLike (formT h t k) h t := .inr ⟨k, rfl⟩

theorem CellLike.hd {x h t : Term} (hx : CellLike x h t) : WSteps (hdT ⬝ x) h := by
  rcases hx with rfl | ⟨k, rfl⟩
  · exact hd_cellT _ _
  · exact hd_form _ _ _

theorem CellLike.tl {x h t : Term} (hx : CellLike x h t) : WSteps (tlT ⬝ x) t := by
  rcases hx with rfl | ⟨k, rfl⟩
  · exact tl_cellT _ _
  · exact tl_form _ _ _

theorem CellLike.force {x h t : Term} (hx : CellLike x h t) (c : Term) :
    WSteps (forceT ⬝ x ⬝ c) (c ⬝ x) := by
  rcases hx with rfl | ⟨k, rfl⟩
  · exact force_cellT _ _ _
  · exact force_form _ _ _ _

/-- `hd` of an atom with **any** bit term is the crash. -/
theorem hd_atomT (b : Term) : WSteps (hdT ⬝ atomT b) errT := by
  have e := BitArith.run hd_atom_run (envR [K, b])
  simp only [OTerm.close, close_toO, close_atomO, close_errO] at e
  exact e

/-- `tl` of an atom with **any** bit term is the crash. -/
theorem tl_atomT (b : Term) : WSteps (tlT ⬝ atomT b) errT := by
  have e := BitArith.run tl_atom_run (envR [K, b])
  simp only [OTerm.close, close_toO, close_atomO, close_errO] at e
  exact e

-- ---------------------------------------------------------------------------
-- The steps
-- ---------------------------------------------------------------------------

/-- Axis 6 of `[h [a t]]` is `a`, for any `h` and `t`. -/
theorem pick6 (h a t : Term) : WSteps (hdT ⬝ (tlT ⬝ cellT h (cellT a t))) a :=
  (WSteps.right _ (tl_cellT _ _)).trans (hd_cellT _ _)

/-- Axis 6 of a cell-like subject. -/
theorem pick6_cl {s B X a C : Term} (hs : CellLike s B X) (hx : CellLike X a C) :
    WSteps (hdT ⬝ (tlT ⬝ s)) a :=
  (WSteps.right _ hs.tl).trans hx.hd

/-- Axis 30 of the loop core is the sample, through the copied subject. -/
theorem pick30 (i : Nat) {s B X a C : Term} (hs : CellLike s B X) (hx : CellLike X a C) :
    WSteps (hdT ⬝ (tlT ⬝ (tlT ⬝ (tlT ⬝ decCore i s)))) a := by
  have h1 : WSteps (tlT ⬝ decCore i s) (cellT (aT i) s) := tl_cellT _ _
  have h2 := (WSteps.right tlT h1).trans (tl_cellT _ _)
  have h3 := (WSteps.right tlT h2).trans hs.tl
  exact (WSteps.right hdT h3).trans hx.hd

/-- `[9 2 …]` on a loop core: pull the battery from axis 2 and run it. -/
theorem dec_pull (i : Nat) (s : Term) :
    WSteps (forceT ⬝ decCore i s ⬝ pullK (atom 2)) (nockToSki hoonDecLoopF ⬝ decCore i s) :=
  (force_cellT _ _ _).trans ((pull2 _).trans
    ((WSteps.left _ (WSteps.right _ (hd_cellT _ _))).trans (app_loopE _)))

/-- The counter, incremented: `[4 0 6]` on a loop core. -/
theorem dec_inc (i : Nat) (s : Term) :
    WSteps (nockToSki (cell (atom 4) (cell (atom 0) (atom 6))) ⬝ decCore i s) (aT (1 + i)) :=
  (step_op4 _ _).trans ((WSteps.right _ ((op0_6 _).trans (pick6 _ _ _))).trans
    (inc_enc_atom (.atom i)))

/-- The loop test `[5 [0 30] [4 0 6]]`: `sam = ctr + 1`. -/
theorem dec_test (i m : Nat) {s B X C : Term} (hs : CellLike s B X) (hx : CellLike X (aT m) C) :
    WSteps (nockToSki (cell (atom 5) (cell (cell (atom 0) (atom 30))
        (cell (atom 4) (cell (atom 0) (atom 6))))) ⬝ decCore i s)
      (encNoun (tisN (atom m) (atom (1 + i)))) := by
  refine (step_op5 _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.right _ ((op0_30 _).trans (pick30 i hs hx)))).trans ?_
  refine (force_enc (.atom m) _).trans ((eqK_beta _ _).trans ?_)
  refine (WSteps.left _ (WSteps.right _ (dec_inc i _))).trans ?_
  exact (force_enc (.atom (1 + i)) _).trans (eq_enc (.atom m) (.atom (1 + i)))

/-- The edit walk at axis 6 of `[bat [j s]]`: forces `bat`, the cell
    `[j s]`, `j`, and `s` to its outer constructor (`hf`); nothing inside
    `s`. -/
theorem dec_editT (bat : Term) {pb : Noun} (hb : Enc pb bat) (j k : Nat) {s : Term}
    (hf : ∀ c, WSteps (forceT ⬝ s ⬝ c) (c ⬝ s)) :
    WSteps (editT [true, false] ⬝ aT k ⬝ cellT bat (cellT (aT j) s))
      (cellT bat (cellT (aT k) s)) := by
  have inner : WSteps (editT [false] ⬝ aT k ⬝ cellT (aT j) s) (cellT (aT k) s) := by
    obtain ⟨k1, h1, hk1⟩ := editT_false [] (aT k) (cellT (aT j) s)
    refine h1.trans ((WSteps.left _ (WSteps.right _ (hd_cellT _ _))).trans
      ((force_enc (.atom j) _).trans ?_))
    obtain ⟨k2, h2, hk2⟩ := hk1 (aT j)
    refine h2.trans ((WSteps.left _ (WSteps.right _ (tl_cellT _ _))).trans ((hf _).trans ?_))
    obtain ⟨k3, h3, hk3⟩ := hk2 s
    refine h3.trans ((WSteps.left _ (WSteps.right _ (.single (.K _ _)))).trans
      ((force_enc (.atom k) _).trans ((hk3 _).trans (CellC_red _ _))))
  obtain ⟨k1, h1, hk1⟩ := editT_true [false] (aT k) (cellT bat (cellT (aT j) s))
  refine h1.trans ((WSteps.left _ (WSteps.right _ (hd_cellT _ _))).trans ((force_enc hb _).trans ?_))
  obtain ⟨k2, h2, hk2⟩ := hk1 bat
  refine h2.trans ((WSteps.left _ (WSteps.right _ (tl_cellT _ _))).trans ((force_cellT _ _ _).trans ?_))
  obtain ⟨k3, h3, hk3⟩ := hk2 (cellT (aT j) s)
  exact h3.trans ((WSteps.left _ (WSteps.right _ inner)).trans
    ((force_cellT _ _ _).trans ((hk3 _).trans (CellC_red _ _))))

theorem editAx_6 : editAx (atom 6) = editT [true, false] := by
  show editT (axisPath (5 + 1)) = _
  rw [axisPath_6]

/-- `[10 [6 [4 0 6]] [0 1]]` on a loop core: the counter incremented in
    place, the copied subject untouched. -/
theorem dec_edit (i : Nat) {s : Term} (hf : ∀ c, WSteps (forceT ⬝ s ⬝ c) (c ⬝ s)) :
    WSteps (nockToSki (cell (atom 10) (cell (cell (atom 6) (cell (atom 4) (cell (atom 0) (atom 6))))
        (cell (atom 0) (atom 1)))) ⬝ decCore i s)
      (decCore (1 + i) s) := by
  refine (step_op10 _ _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.right _ (op0_1 _))).trans ((force_cellT _ _ _).trans ?_)
  obtain ⟨kv, h1, hkv⟩ := editK_beta (atom 6)
    (nockToSki (cell (atom 4) (cell (atom 0) (atom 6))) ⬝ decCore i s) (decCore i s)
  refine h1.trans ((WSteps.left _ (WSteps.right _ (dec_inc i _))).trans
    ((force_enc (.atom (1 + i)) _).trans ((hkv _).trans ?_)))
  rw [editAx_6]
  exact dec_editT loopE loopE_enc i (1 + i) hf

/-- **The loop**: from counter `i`, with `i + 1 + k = m`, the loop returns
    `⟨i + k⟩ = ⟨m - 1⟩`; the subject rides along in the core. -/
theorem dec_loop (m : Nat) {s B X C : Term} (hs : CellLike s B X) (hx : CellLike X (aT m) C) :
    ∀ k i, i + 1 + k = m → WSteps (nockToSki hoonDecLoopF ⬝ decCore i s) (aT (i + k)) := by
  intro k
  induction k with
  | zero =>
    intro i hm
    rw [hoonDecLoopF_split]
    refine (step_op6 _ _ _ _).trans ?_
    have ht : tisN (atom m) (atom (1 + i)) = atom 0 := by
      rw [tisN, if_pos (by rw [← hm]; congr 1; omega)]
    have hT := dec_test i m hs hx
    rw [ht] at hT
    refine (WSteps.left _ (WSteps.left _ (WSteps.right _ hT))).trans ?_
    refine (ifn_enc_zero (.atom 0) _ _).trans ((op0_6 _).trans ?_)
    exact pick6 _ _ _
  | succ k ih =>
    intro i hm
    have hrec := ih (1 + i) (by omega)
    rw [show 1 + i + k = i + (k + 1) by omega] at hrec
    rw [hoonDecLoopF_split]
    refine (step_op6 _ _ _ _).trans ?_
    have ht : tisN (atom m) (atom (1 + i)) = atom 1 := by
      rw [tisN, if_neg (by intro h; cases h; omega)]
    have hT := dec_test i m hs hx
    rw [ht] at hT
    refine (WSteps.left _ (WSteps.left _ (WSteps.right _ hT))).trans ?_
    refine (ifn_enc_one (.atom 1) _ _).trans ((step_op9 _ _ _).trans ?_)
    refine (WSteps.left _ (WSteps.right _ (dec_edit i hs.force))).trans ?_
    exact (dec_pull _ _).trans hrec

/-- The guard `[5 [1 0] [0 6]]`, given what axis 6 reduces to. -/
theorem dec_guard_gen {s e : Term} (h6 : WSteps (hdT ⬝ (tlT ⬝ s)) e) :
    WSteps (nockToSki (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 6)))) ⬝ s)
      (forceT ⬝ e ⬝ (eqT ⬝ encLit (atom 0))) := by
  refine (step_op5 _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.right _ (step_op1 _ _))).trans ?_
  refine (force_enc (enc_encLit (atom 0)) _).trans ((eqK_beta _ _).trans ?_)
  exact WSteps.left _ (WSteps.right _ ((op0_6 _).trans h6))

/-- The guard on a cell-like core with sample `⟨m⟩`: `m = 0`. -/
theorem dec_guard (m : Nat) {s B X C : Term} (hs : CellLike s B X) (hx : CellLike X (aT m) C) :
    WSteps (nockToSki (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 6)))) ⬝ s)
      (encNoun (tisN (atom 0) (atom m))) :=
  (dec_guard_gen (pick6_cl hs hx)).trans
    ((force_enc (.atom m) _).trans (eq_enc (enc_encLit (atom 0)) (.atom m)))

/-- The arm crashes wherever axis 6 crashes. -/
theorem dec_body_err {s : Term} (h6 : WSteps (hdT ⬝ (tlT ⬝ s)) errT) :
    WSteps (nockToSki hoonDecBodyF ⬝ s) errT := by
  rw [hoonDecBodyF_split]
  refine (step_op6 _ _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.left _ (WSteps.right _
    ((dec_guard_gen h6).trans (force_err _))))).trans ?_
  exact ifn_err _ _

/-- The compiled arm on a cell-like core `[B [⟨n+1⟩ C]]`. -/
theorem hoon_dec_body_cl {s B X C : Term} {n : Nat} (hs : CellLike s B X)
    (hx : CellLike X (aT (n + 1)) C) : WSteps (nockToSki hoonDecBodyF ⬝ s) (aT n) := by
  rw [hoonDecBodyF_split]
  refine (step_op6 _ _ _ _).trans ?_
  have ht : tisN (atom 0) (atom (n + 1)) = atom 1 := by
    rw [tisN, if_neg (by intro h; cases h)]
  have hG := dec_guard (n + 1) hs hx
  rw [ht] at hG
  refine (WSteps.left _ (WSteps.left _ (WSteps.right _ hG))).trans ?_
  refine (ifn_enc_one (.atom 1) _ _).trans ?_
  -- push the counter `0`
  refine (step_op8 _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.right _ (step_op1 _ _))).trans ?_
  refine (force_enc (enc_encLit (atom 0)) _).trans ((pushK_beta _ _ _).trans ?_)
  -- push the loop battery
  refine (step_op8 _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.right _ (step_op1 _ _))).trans ?_
  refine (force_enc (enc_encLit hoonDecLoopF) _).trans ((pushK_beta _ _ _).trans ?_)
  -- the core is `decCore 0 s`
  have h0 : encLit (atom 0) = aT 0 := (enc_encLit (atom 0)).atom_inv
  have hcore : WSteps (CellC ⬝ encLit hoonDecLoopF ⬝ (CellC ⬝ encLit (atom 0) ⬝ s)) (decCore 0 s) := by
    refine (WSteps.right _ (CellC_red _ _)).trans ?_
    rw [h0]
    exact CellC_red _ _
  refine (WSteps.right _ hcore).trans ?_
  -- pull and run the loop
  refine (step_op9 _ _ _).trans ((WSteps.left _ (WSteps.right _ (op0_1 _))).trans ((dec_pull _ _).trans ?_))
  have h := dec_loop (n + 1) hs hx n 0 (by omega)
  rw [Nat.zero_add] at h
  exact h

/-- The compiled arm on a cell-like core with sample `⟨0⟩`: the guard's crash. -/
theorem hoon_dec_body_cl_zero {s B X C : Term} (hs : CellLike s B X) (hx : CellLike X (aT 0) C) :
    WSteps (nockToSki hoonDecBodyF ⬝ s) errT := by
  rw [hoonDecBodyF_split]
  refine (step_op6 _ _ _ _).trans ?_
  have ht : tisN (atom 0) (atom 0) = atom 0 := by rw [tisN, if_pos rfl]
  have hG := dec_guard 0 hs hx
  rw [ht] at hG
  refine (WSteps.left _ (WSteps.left _ (WSteps.right _ hG))).trans ?_
  exact (ifn_enc_zero (.atom 0) _ _).trans (step_op0_zero _)

-- ---------------------------------------------------------------------------
-- (b) The jet, independent of axes 2 and 7 and of the code of a `Form`
-- ---------------------------------------------------------------------------

/-- **(b), general**: the outer cell `[B X]` and the inner `[⟨n+1⟩ C]` each
    a `cellT` or a `formT` with any code; `B`, `C` and the codes any terms. -/
theorem hoon_dec_free_cl {s B X C : Term} {n : Nat} (hs : CellLike s B X)
    (hx : CellLike X (encNoun (atom (n + 1))) C) :
    WSteps (jetT hoonDecBodyF ⬝ s) (encNoun (atom n)) :=
  (jetT_red _ _).trans ((WSteps.right _ (hoon_dec_body_cl hs hx)).trans (toCell_enc (.atom n)))

/-- **(b), underflow, general**: sample `⟨0⟩` gives `Err`. -/
theorem hoon_dec_free_cl_zero {s B X C : Term} (hs : CellLike s B X)
    (hx : CellLike X (encNoun (atom 0)) C) : WSteps (jetT hoonDecBodyF ⬝ s) errT :=
  (jetT_red _ _).trans ((WSteps.right _ (hoon_dec_body_cl_zero hs hx)).trans toCell_err)

/-- **(b)** The jet on `[B [⟨n+1⟩ C]]` for any closed terms `B`, `C`. -/
theorem hoon_dec_free (B C : Term) (n : Nat) :
    WSteps (jetT hoonDecBodyF ⬝ cellT B (cellT (encNoun (atom (n + 1))) C)) (encNoun (atom n)) :=
  hoon_dec_free_cl (.cell _ _) (.cell _ _)

/-- **(b)**, both cells `Form`s with any codes `K₁`, `K₂`. -/
theorem hoon_dec_free_form (B C K₁ K₂ : Term) (n : Nat) :
    WSteps (jetT hoonDecBodyF ⬝ formT B (formT (encNoun (atom (n + 1))) C K₂) K₁)
      (encNoun (atom n)) :=
  hoon_dec_free_cl (.form _ _ _) (.form _ _ _)

/-- **(b), underflow**: `[B [⟨0⟩ C]]` gives `Err`. -/
theorem hoon_dec_free_zero (B C : Term) :
    WSteps (jetT hoonDecBodyF ⬝ cellT B (cellT (encNoun (atom 0)) C)) errT :=
  hoon_dec_free_cl_zero (.cell _ _) (.cell _ _)

/-- **Err (i)**: the core an atom, with **any** bit term `b`. -/
theorem hoon_dec_err_atom (b : Term) : WSteps (jetT hoonDecBodyF ⬝ atomT b) errT :=
  (jetT_red _ _).trans ((WSteps.right _ (dec_body_err
    ((WSteps.right _ (tl_atomT b)).trans hd_err))).trans toCell_err)

/-- **Err (ii)**: the core `[B atom]` (cell-like, any code), the atom with
    **any** bit term `b`. -/
theorem hoon_dec_err_noSample {s B : Term} (b : Term) (hs : CellLike s B (atomT b)) :
    WSteps (jetT hoonDecBodyF ⬝ s) errT :=
  (jetT_red _ _).trans ((WSteps.right _ (dec_body_err
    ((WSteps.right _ hs.tl).trans (hd_atomT b)))).trans toCell_err)

/-- `[B ⟨t⟩]`, the canonical instance of Err (ii). -/
theorem hoon_dec_free_noSample (B : Term) (t : Nat) :
    WSteps (jetT hoonDecBodyF ⬝ cellT B (encNoun (atom t))) errT :=
  hoon_dec_err_noSample _ (.cell _ _)

-- ---------------------------------------------------------------------------
-- The fire check
-- ---------------------------------------------------------------------------

/-- The fields of a term that is literally `cellT h t` or `formT h t k`. -/
def cellParts? : Term → Option (Term × Term)
  | K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ h)) ⬝ (K ⬝ t)))) => some (h, t)
  | K ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ h)) ⬝ (K ⬝ t)) ⬝ (K ⬝ _)))) => some (h, t)
  | _ => none

theorem cellParts?_cellT (h t : Term) : cellParts? (cellT h t) = some (h, t) := rfl
theorem cellParts?_formT (h t k : Term) : cellParts? (formT h t k) = some (h, t) := rfl

/-- The bit list of a term that is literally `atomT b`. -/
def atomBits? : Term → Option Term
  | S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ I ⬝ (K ⬝ b)))) => some b
  | _ => none

/-- The bits of a term that is literally `bl bs`. -/
def blBits? : Term → Option (List Bool)
  | K => some []
  | K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ K)) ⬝ (K ⬝ t)) => (blBits? t).map (true :: ·)
  | K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ (K ⬝ I))) ⬝ (K ⬝ t)) => (blBits? t).map (false :: ·)
  | _ => none

/-- The number a term that is literally the canonical atom `⟨m⟩` encodes. -/
def atomNat? (a : Term) : Option Nat :=
  match atomBits? a with
  | none => none
  | some b => match blBits? b with
    | none => none
    | some bs => if bits (BitArith.val bs) = bs then some (BitArith.val bs) else none

/-- **The sample the fire check reads**: `some m` when the term is literally
    a cell-like `[B [⟨m⟩ C]]` (each cell a `cellT` or a `formT`), `⟨m⟩`
    canonical. -/
def hoonDecSample? (t : Term) : Option Nat :=
  match cellParts? t with
  | none => none
  | some (_, x) => match cellParts? x with
    | none => none
    | some (a, _) => atomNat? a

/-- **The fire predicate** (value, or `Err` at sample `0`): a canonical atom
    sample of at most 32 bits. -/
def HoonDecFires (t : Term) : Prop := ∃ m, hoonDecSample? t = some m ∧ m < 2 ^ 32

instance (t : Term) : Decidable (HoonDecFires t) :=
  match h : hoonDecSample? t with
  | none => isFalse (fun ⟨_, hm, _⟩ => by rw [h] at hm; cases hm)
  | some m =>
    if hlt : m < 2 ^ 32 then isTrue ⟨m, h, hlt⟩
    else isFalse (fun ⟨m', hm, hl⟩ => by rw [h] at hm; cases hm; exact hlt hl)

/-- **The `Err` shapes**: the term is literally an atom (any bit term), or
    literally a cell-like `[B atom]` (any bit term). -/
def hoonDecErr? (t : Term) : Bool :=
  match atomBits? t with
  | some _ => true
  | none => match cellParts? t with
    | some (_, x) => (atomBits? x).isSome
    | none => false

/-- **The `Err` fire predicate.** -/
def HoonDecErrFires (t : Term) : Prop := hoonDecErr? t = true

instance (t : Term) : Decidable (HoonDecErrFires t) :=
  inferInstanceAs (Decidable (hoonDecErr? t = true))

/-- The outcome on a sample: `m - 1`, or the crash at `0`. -/
def hoonDecOutN : Nat → Outcome
  | 0 => .exit
  | n + 1 => .val (atom n)

theorem hoonDecOutN_eq (b c : Noun) (m : Nat) : hoonDecOutN m = hoonDecC (cell b (cell (atom m) c)) := by
  cases m <;> rfl

/-- **The whole check**: `some u` to fire with output `u`, `none` to decline. -/
def hoonDecFire? (t : Term) : Option Term :=
  if hoonDecErr? t then some errT
  else match hoonDecSample? t with
    | some m => if m < 2 ^ 32 then some (encOut (hoonDecOutN m)) else none
    | none => none

theorem cellParts?_sound {t h x : Term} (e : cellParts? t = some (h, x)) : CellLike t h x := by
  unfold cellParts? at e
  split at e
  · cases e; exact .cell _ _
  · cases e; exact .form _ _ _
  · cases e

theorem atomBits?_sound {a b : Term} (e : atomBits? a = some b) : a = atomT b := by
  unfold atomBits? at e
  split at e
  · cases e; rfl
  · cases e

theorem blBits?_sound : ∀ {b : Term} {bs : List Bool}, blBits? b = some bs → b = BitArith.bl bs := by
  intro b
  induction b using blBits?.induct with
  | case1 => intro bs e; simp only [blBits?, Option.some.injEq] at e; subst e; rfl
  | case2 t ih =>
    intro bs e
    simp only [blBits?, Option.map_eq_some_iff] at e
    obtain ⟨cs, hc, rfl⟩ := e
    rw [ih hc]; rfl
  | case3 t ih =>
    intro bs e
    simp only [blBits?, Option.map_eq_some_iff] at e
    obtain ⟨cs, hc, rfl⟩ := e
    rw [ih hc]; rfl
  | case4 t h1 h2 h3 =>
    intro bs e
    rw [blBits?] at e
    · cases e
    all_goals assumption

theorem atomNat?_sound {a : Term} {m : Nat} (e : atomNat? a = some m) : a = aT m := by
  unfold atomNat? at e
  split at e
  · cases e
  · rename_i b hb
    split at e
    · cases e
    · rename_i bs hbs
      split at e
      · rename_i hc
        cases e
        rw [atomBits?_sound hb, blBits?_sound hbs, aT, encNoun_atom, hc]
      · cases e

/-- **What the sample check accepts**: a cell-like `[B [⟨m⟩ C]]`, literally. -/
theorem hoonDecSample?_sound {t : Term} {m : Nat} (e : hoonDecSample? t = some m) :
    ∃ B X C, CellLike t B X ∧ CellLike X (aT m) C := by
  unfold hoonDecSample? at e
  split at e
  · cases e
  · rename_i B x hx
    split at e
    · cases e
    · rename_i a C ha
      rw [atomNat?_sound e] at ha
      exact ⟨B, x, C, cellParts?_sound hx, cellParts?_sound ha⟩

theorem blBits?_bl : ∀ bs : List Bool, blBits? (BitArith.bl bs) = some bs
  | [] => rfl
  | true :: bs => by
    show (blBits? (BitArith.bl bs)).map (true :: ·) = _
    rw [blBits?_bl bs]; rfl
  | false :: bs => by
    show (blBits? (BitArith.bl bs)).map (false :: ·) = _
    rw [blBits?_bl bs]; rfl

theorem atomNat?_aT (m : Nat) : atomNat? (aT m) = some m := by
  show (match blBits? (BitArith.bl (bits m)) with
    | none => none
    | some bs => if bits (BitArith.val bs) = bs then some (BitArith.val bs) else none) = some m
  rw [blBits?_bl]
  simp [val_bits]

/-- **The sample check accepts every real core**: on `cellT`/`formT` of
    `[B [⟨m⟩ C]]` it reads `m`, whatever `B`, `C` and the codes are. -/
theorem hoonDecSample?_cl {t B X C : Term} {m : Nat} (ht : CellLike t B X)
    (hx : CellLike X (aT m) C) : hoonDecSample? t = some m := by
  rcases ht with rfl | ⟨k, rfl⟩ <;> rcases hx with rfl | ⟨k', rfl⟩ <;> exact atomNat?_aT m

theorem hoonDecSample?_cellT (B C : Term) (m : Nat) :
    hoonDecSample? (cellT B (cellT (aT m) C)) = some m :=
  hoonDecSample?_cl (.cell _ _) (.cell _ _)

/-- **The sample check is sound**. -/
theorem hoon_dec_fires_sound {t : Term} {m : Nat} (e : hoonDecSample? t = some m) :
    WSteps (jetT hoonDecBodyF ⬝ t) (encOut (hoonDecOutN m)) := by
  obtain ⟨B, X, C, ht, hx⟩ := hoonDecSample?_sound e
  cases m with
  | zero => exact hoon_dec_free_cl_zero ht hx
  | succ n => exact hoon_dec_free_cl ht hx

/-- **`HoonDecFires` is sound**. -/
theorem hoon_dec_fires {t : Term} (h : HoonDecFires t) :
    ∃ m, hoonDecSample? t = some m ∧ m < 2 ^ 32 ∧
      WSteps (jetT hoonDecBodyF ⬝ t) (encOut (hoonDecOutN m)) :=
  let ⟨m, e, hm⟩ := h
  ⟨m, e, hm, hoon_dec_fires_sound e⟩

/-- **`HoonDecErrFires` is sound**: on the `Err` shapes the term reaches `Err`. -/
theorem hoon_dec_err_fires {t : Term} (h : HoonDecErrFires t) :
    WSteps (jetT hoonDecBodyF ⬝ t) errT := by
  unfold HoonDecErrFires hoonDecErr? at h
  split at h
  · rename_i b hb
    rw [atomBits?_sound hb]
    exact hoon_dec_err_atom b
  · split at h
    · rename_i B x hx
      cases hb : atomBits? x with
      | none => rw [hb] at h; cases h
      | some b =>
        have hs := cellParts?_sound hx
        rw [atomBits?_sound hb] at hs
        exact hoon_dec_err_noSample b hs
    · cases h

/-- **The whole check is sound**: whenever it fires, its output is the
    term's own reduct. -/
theorem hoon_dec_fire_sound {t u : Term} (e : hoonDecFire? t = some u) :
    WSteps (jetT hoonDecBodyF ⬝ t) u := by
  unfold hoonDecFire? at e
  split at e
  · rename_i h
    cases e
    exact hoon_dec_err_fires h
  · split at e
    · rename_i m hm
      split at e
      · cases e; exact hoon_dec_fires_sound hm
      · cases e
    · cases e

/-- The check, pinned by kernel evaluation: it fires on canonical samples
    whatever the other fields, with either cell a `Form`; fires `Err` on an
    atom core and on `[B atom]` with any bits, `Form` or not; and declines at
    `2^32`, on a non-canonical sample (`[1 0]`, a trailing `false`) and on a
    cell sample. -/
theorem hoonDecFires_pins :
    hoonDecFire? (cellT S (cellT (aT 5) K)) = some (aT 4) ∧
    hoonDecFire? (formT S (cellT (aT 5) K) I) = some (aT 4) ∧
    hoonDecFire? (cellT S (formT (aT 5) K (S ⬝ S)) ) = some (aT 4) ∧
    hoonDecFire? (formT S (formT (aT 5) K I) (S ⬝ S)) = some (aT 4) ∧
    hoonDecFire? (cellT S (cellT (aT 0) K)) = some errT ∧
    hoonDecFire? (atomT (S ⬝ K)) = some errT ∧
    hoonDecFire? (cellT S (atomT (BitArith.bl [true, false]))) = some errT ∧
    hoonDecFire? (formT S (atomT I) K) = some errT ∧
    hoonDecFire? (cellT S (cellT (aT (2 ^ 32)) K)) = none ∧
    hoonDecFire? (cellT S (cellT (atomT (BitArith.bl [true, false])) K)) = none ∧
    hoonDecFire? (cellT S (cellT (cellT K K) K)) = none ∧
    HoonDecFires (formT S (formT (aT 5) K I) I) ∧
    HoonDecErrFires (formT S (atomT I) K) ∧
    ¬ HoonDecErrFires (cellT S (cellT (aT 0) K)) := by decide +kernel

end Nock2Ski
