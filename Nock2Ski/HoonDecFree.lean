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
- **(b) any terms at axes 2 and 7**: for arbitrary closed terms `B` and `C`,
  no `Enc` hypothesis, on the subject `cellT B (cellT ⟨m⟩ C)` with the
  sample the canonical atom `⟨m⟩ = encNoun (atom m)`:
  `hoon_dec_free` (`m = n + 1` gives `⟨n⟩`), `hoon_dec_free_zero`
  (`m = 0` gives `Err`), and `hoon_dec_free_noSample` (`cellT B ⟨t⟩`, no
  axis 6, gives `Err`).  A cell sample is excluded: there the arm diverges
  (`hoon_dec_off_domain_term`).

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

**The fire check** (`HoonDecFires`, decidable): the term is literally
`cellT B (cellT a C)`, `a` literally `atomT (bl bs)`, `bs` canonical
(`bits (val bs) = bs`, no trailing `false`), and `val bs < 2^32`;
`hoonDecSample? t` returns that `m = val bs`.  `hoon_dec_fires_sound`: on a
term the check accepts, `jetT hoonDecBodyF ⬝ t ↠ encOut (hoonDecOutN m)`,
`⟨m - 1⟩` for `m ≥ 1` and `Err` at `0`.  `hoonDecSample?_cellT`: the
check accepts every `cellT B (cellT ⟨m⟩ C)`, whatever `B` and `C` are.
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

/-- Axis 6 of `[h [a t]]` is `a`, for any `h` and `t`. -/
theorem pick6 (h a t : Term) : WSteps (hdT ⬝ (tlT ⬝ cellT h (cellT a t))) a :=
  (WSteps.right _ (tl_cellT _ _)).trans (hd_cellT _ _)

/-- Axis 30 of the loop core is the sample, through the copied subject. -/
theorem pick30 (i m : Nat) (B C : Term) :
    WSteps (hdT ⬝ (tlT ⬝ (tlT ⬝ (tlT ⬝ decCore i (cellT B (cellT (aT m) C)))))) (aT m) := by
  have h1 : WSteps (tlT ⬝ decCore i (cellT B (cellT (aT m) C))) (cellT (aT i) (cellT B (cellT (aT m) C))) :=
    tl_cellT _ _
  have h2 := (WSteps.right tlT h1).trans (tl_cellT _ _)
  have h3 := (WSteps.right tlT h2).trans (tl_cellT _ _)
  exact (WSteps.right hdT h3).trans (hd_cellT _ _)

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
theorem dec_test (i m : Nat) (B C : Term) :
    WSteps (nockToSki (cell (atom 5) (cell (cell (atom 0) (atom 30))
        (cell (atom 4) (cell (atom 0) (atom 6))))) ⬝ decCore i (cellT B (cellT (aT m) C)))
      (encNoun (tisN (atom m) (atom (1 + i)))) := by
  refine (step_op5 _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.right _ ((op0_30 _).trans (pick30 i m B C)))).trans ?_
  refine (force_enc (.atom m) _).trans ((eqK_beta _ _).trans ?_)
  refine (WSteps.left _ (WSteps.right _ (dec_inc i _))).trans ?_
  exact (force_enc (.atom (1 + i)) _).trans (eq_enc (.atom m) (.atom (1 + i)))

/-- The edit walk at axis 6 of `[bat [j [B X]]]`: forces `bat`, the cell
    `[j [B X]]`, `j`, and `[B X]` to its outer constructor; never `B`
    or `X`. -/
theorem dec_editT (bat : Term) {pb : Noun} (hb : Enc pb bat) (j k : Nat) (B X : Term) :
    WSteps (editT [true, false] ⬝ aT k ⬝ cellT bat (cellT (aT j) (cellT B X)))
      (cellT bat (cellT (aT k) (cellT B X))) := by
  -- the inner level, at `[j [B X]]`
  have inner : WSteps (editT [false] ⬝ aT k ⬝ cellT (aT j) (cellT B X)) (cellT (aT k) (cellT B X)) := by
    obtain ⟨k1, h1, hk1⟩ := editT_false [] (aT k) (cellT (aT j) (cellT B X))
    refine h1.trans ((WSteps.left _ (WSteps.right _ (hd_cellT _ _))).trans
      ((force_enc (.atom j) _).trans ?_))
    obtain ⟨k2, h2, hk2⟩ := hk1 (aT j)
    refine h2.trans ((WSteps.left _ (WSteps.right _ (tl_cellT _ _))).trans
      ((force_cellT _ _ _).trans ?_))
    obtain ⟨k3, h3, hk3⟩ := hk2 (cellT B X)
    refine h3.trans ((WSteps.left _ (WSteps.right _ (.single (.K _ _)))).trans
      ((force_enc (.atom k) _).trans ((hk3 _).trans (CellC_red _ _))))
  obtain ⟨k1, h1, hk1⟩ := editT_true [false] (aT k) (cellT bat (cellT (aT j) (cellT B X)))
  refine h1.trans ((WSteps.left _ (WSteps.right _ (hd_cellT _ _))).trans ((force_enc hb _).trans ?_))
  obtain ⟨k2, h2, hk2⟩ := hk1 bat
  refine h2.trans ((WSteps.left _ (WSteps.right _ (tl_cellT _ _))).trans ((force_cellT _ _ _).trans ?_))
  obtain ⟨k3, h3, hk3⟩ := hk2 (cellT (aT j) (cellT B X))
  exact h3.trans ((WSteps.left _ (WSteps.right _ inner)).trans
    ((force_cellT _ _ _).trans ((hk3 _).trans (CellC_red _ _))))

theorem editAx_6 : editAx (atom 6) = editT [true, false] := by
  show editT (axisPath (5 + 1)) = _
  rw [axisPath_6]

/-- `[10 [6 [4 0 6]] [0 1]]` on a loop core: the counter incremented in
    place, the copied subject untouched. -/
theorem dec_edit (i : Nat) (B X : Term) :
    WSteps (nockToSki (cell (atom 10) (cell (cell (atom 6) (cell (atom 4) (cell (atom 0) (atom 6))))
        (cell (atom 0) (atom 1)))) ⬝ decCore i (cellT B X))
      (decCore (1 + i) (cellT B X)) := by
  refine (step_op10 _ _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.right _ (op0_1 _))).trans ((force_cellT _ _ _).trans ?_)
  obtain ⟨kv, h1, hkv⟩ := editK_beta (atom 6)
    (nockToSki (cell (atom 4) (cell (atom 0) (atom 6))) ⬝ decCore i (cellT B X)) (decCore i (cellT B X))
  refine h1.trans ((WSteps.left _ (WSteps.right _ (dec_inc i _))).trans
    ((force_enc (.atom (1 + i)) _).trans ((hkv _).trans ?_)))
  rw [editAx_6]
  exact dec_editT loopE loopE_enc i (1 + i) B X

/-- **The loop**: from counter `i`, with `i + 1 + k = m`, the loop returns
    `⟨i + k⟩ = ⟨m - 1⟩`; `B` and `C` ride along in the copied subject. -/
theorem dec_loop (m : Nat) (B C : Term) :
    ∀ k i, i + 1 + k = m →
      WSteps (nockToSki hoonDecLoopF ⬝ decCore i (cellT B (cellT (aT m) C))) (aT (i + k)) := by
  intro k
  induction k with
  | zero =>
    intro i hm
    rw [hoonDecLoopF_split]
    refine (step_op6 _ _ _ _).trans ?_
    have ht : tisN (atom m) (atom (1 + i)) = atom 0 := by
      rw [tisN, if_pos (by rw [← hm]; congr 1; omega)]
    have hT := dec_test i m B C
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
    have hT := dec_test i m B C
    rw [ht] at hT
    refine (WSteps.left _ (WSteps.left _ (WSteps.right _ hT))).trans ?_
    refine (ifn_enc_one (.atom 1) _ _).trans ((step_op9 _ _ _).trans ?_)
    refine (WSteps.left _ (WSteps.right _ (dec_edit i B (cellT (aT m) C)))).trans ?_
    exact (dec_pull _ _).trans hrec

/-- The guard `[5 [1 0] [0 6]]` on `[B [⟨m⟩ C]]`: `m = 0`. -/
theorem dec_guard (m : Nat) (B C : Term) :
    WSteps (nockToSki (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 6))))
        ⬝ cellT B (cellT (aT m) C))
      (encNoun (tisN (atom 0) (atom m))) := by
  refine (step_op5 _ _ _).trans ?_
  refine (WSteps.left _ (WSteps.right _ (step_op1 _ _))).trans ?_
  refine (force_enc (enc_encLit (atom 0)) _).trans ((eqK_beta _ _).trans ?_)
  refine (WSteps.left _ (WSteps.right _ ((op0_6 _).trans (pick6 _ _ _)))).trans ?_
  exact (force_enc (.atom m) _).trans (eq_enc (enc_encLit (atom 0)) (.atom m))

/-- The compiled arm on `[B [⟨n+1⟩ C]]`, `B` and `C` any terms. -/
theorem hoon_dec_body_free (B C : Term) (n : Nat) :
    WSteps (nockToSki hoonDecBodyF ⬝ cellT B (cellT (aT (n + 1)) C)) (aT n) := by
  rw [hoonDecBodyF_split]
  refine (step_op6 _ _ _ _).trans ?_
  have ht : tisN (atom 0) (atom (n + 1)) = atom 1 := by
    rw [tisN, if_neg (by intro h; cases h)]
  have hG := dec_guard (n + 1) B C
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
  -- the core is `decCore 0 S`
  have h0 : encLit (atom 0) = aT 0 := (enc_encLit (atom 0)).atom_inv
  have hcore : WSteps (CellC ⬝ encLit hoonDecLoopF ⬝ (CellC ⬝ encLit (atom 0) ⬝ cellT B (cellT (aT (n + 1)) C)))
      (decCore 0 (cellT B (cellT (aT (n + 1)) C))) := by
    refine (WSteps.right _ (CellC_red _ _)).trans ?_
    rw [h0]
    exact CellC_red _ _
  refine (WSteps.right _ hcore).trans ?_
  -- pull and run the loop
  refine (step_op9 _ _ _).trans ((WSteps.left _ (WSteps.right _ (op0_1 _))).trans ((dec_pull _ _).trans ?_))
  have h := dec_loop (n + 1) B C n 0 (by omega)
  rw [Nat.zero_add] at h
  exact h

/-- The compiled arm on `[B [⟨0⟩ C]]`: the guard's crash. -/
theorem hoon_dec_body_free_zero (B C : Term) :
    WSteps (nockToSki hoonDecBodyF ⬝ cellT B (cellT (aT 0) C)) errT := by
  rw [hoonDecBodyF_split]
  refine (step_op6 _ _ _ _).trans ?_
  have ht : tisN (atom 0) (atom 0) = atom 0 := by rw [tisN, if_pos rfl]
  have hG := dec_guard 0 B C
  rw [ht] at hG
  refine (WSteps.left _ (WSteps.left _ (WSteps.right _ hG))).trans ?_
  exact (ifn_enc_zero (.atom 0) _ _).trans (step_op0_zero _)

/-- The compiled arm on `[B ⟨t⟩]`: no axis 6, the crash. -/
theorem hoon_dec_body_free_noSample (B : Term) (t : Nat) :
    WSteps (nockToSki hoonDecBodyF ⬝ cellT B (aT t)) errT := by
  rw [hoonDecBodyF_split]
  refine (step_op6 _ _ _ _).trans ?_
  have hG : WSteps (nockToSki (cell (atom 5) (cell (cell (atom 1) (atom 0)) (cell (atom 0) (atom 6))))
      ⬝ cellT B (aT t)) errT := by
    refine (step_op5 _ _ _).trans ?_
    refine (WSteps.left _ (WSteps.right _ (step_op1 _ _))).trans ?_
    refine (force_enc (enc_encLit (atom 0)) _).trans ((eqK_beta _ _).trans ?_)
    refine (WSteps.left _ (WSteps.right _ ((op0_6 _).trans
      ((WSteps.right _ (tl_cellT _ _)).trans (hd_enc_atom (.atom t)))))).trans ?_
    exact force_err _
  refine (WSteps.left _ (WSteps.left _ (WSteps.right _ hG))).trans ?_
  exact ifn_err _ _

-- ---------------------------------------------------------------------------
-- (b) The jet, independent of axes 2 and 7
-- ---------------------------------------------------------------------------

/-- **(b)** The jet on `[B [⟨n+1⟩ C]]` for any closed terms `B`, `C`: the
    battery slot and the context are never forced. -/
theorem hoon_dec_free (B C : Term) (n : Nat) :
    WSteps (jetT hoonDecBodyF ⬝ cellT B (cellT (encNoun (atom (n + 1))) C)) (encNoun (atom n)) :=
  (jetT_red _ _).trans ((WSteps.right _ (hoon_dec_body_free B C n)).trans (toCell_enc (.atom n)))

/-- **(b), underflow**: `[B [⟨0⟩ C]]` gives `Err`. -/
theorem hoon_dec_free_zero (B C : Term) :
    WSteps (jetT hoonDecBodyF ⬝ cellT B (cellT (encNoun (atom 0)) C)) errT :=
  (jetT_red _ _).trans ((WSteps.right _ (hoon_dec_body_free_zero B C)).trans toCell_err)

/-- **(b), no sample**: `[B ⟨t⟩]` gives `Err`. -/
theorem hoon_dec_free_noSample (B : Term) (t : Nat) :
    WSteps (jetT hoonDecBodyF ⬝ cellT B (encNoun (atom t))) errT :=
  (jetT_red _ _).trans ((WSteps.right _ (hoon_dec_body_free_noSample B t)).trans toCell_err)

-- ---------------------------------------------------------------------------
-- The fire check
-- ---------------------------------------------------------------------------

/-- The fields of a term that is literally `cellT h t`. -/
def cellParts? : Term → Option (Term × Term)
  | K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ h)) ⬝ (K ⬝ t)))) => some (h, t)
  | _ => none

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

/-- **The sample the fire check reads**: `some m` when the term is
    literally `cellT B (cellT ⟨m⟩ C)`, `⟨m⟩` canonical. -/
def hoonDecSample? (t : Term) : Option Nat :=
  match cellParts? t with
  | none => none
  | some (_, x) => match cellParts? x with
    | none => none
    | some (a, _) => atomNat? a

/-- **The fire predicate**: a canonical atom sample of at most 32 bits. -/
def HoonDecFires (t : Term) : Prop := ∃ m, hoonDecSample? t = some m ∧ m < 2 ^ 32

instance (t : Term) : Decidable (HoonDecFires t) :=
  match h : hoonDecSample? t with
  | none => isFalse (fun ⟨_, hm, _⟩ => by rw [h] at hm; cases hm)
  | some m =>
    if hlt : m < 2 ^ 32 then isTrue ⟨m, h, hlt⟩
    else isFalse (fun ⟨m', hm, hl⟩ => by rw [h] at hm; cases hm; exact hlt hl)

/-- The outcome on a sample: `m - 1`, or the crash at `0`. -/
def hoonDecOutN : Nat → Outcome
  | 0 => .exit
  | n + 1 => .val (atom n)

theorem hoonDecOutN_eq (b c : Noun) (m : Nat) : hoonDecOutN m = hoonDecC (cell b (cell (atom m) c)) := by
  cases m <;> rfl

theorem cellParts?_sound {t h x : Term} (e : cellParts? t = some (h, x)) : t = cellT h x := by
  unfold cellParts? at e
  split at e
  · cases e; rfl
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

/-- **What the fire check accepts**: `cellT B (cellT ⟨m⟩ C)`, literally. -/
theorem hoonDecSample?_sound {t : Term} {m : Nat} (e : hoonDecSample? t = some m) :
    ∃ B C, t = cellT B (cellT (aT m) C) := by
  unfold hoonDecSample? at e
  split at e
  · cases e
  · rename_i B x hx
    split at e
    · cases e
    · rename_i a C ha
      exact ⟨B, C, by rw [cellParts?_sound hx, cellParts?_sound ha, atomNat?_sound e]⟩

theorem blBits?_bl : ∀ bs : List Bool, blBits? (BitArith.bl bs) = some bs
  | [] => rfl
  | true :: bs => by
    show (blBits? (BitArith.bl bs)).map (true :: ·) = _
    rw [blBits?_bl bs]; rfl
  | false :: bs => by
    show (blBits? (BitArith.bl bs)).map (false :: ·) = _
    rw [blBits?_bl bs]; rfl

/-- **The fire check accepts every real core**: on `cellT B (cellT ⟨m⟩ C)`
    it reads `m`, whatever `B` and `C` are. -/
theorem hoonDecSample?_cellT (B C : Term) (m : Nat) :
    hoonDecSample? (cellT B (cellT (aT m) C)) = some m := by
  show atomNat? (atomT (BitArith.bl (bits m))) = some m
  unfold atomNat?
  show (match blBits? (BitArith.bl (bits m)) with
    | none => none
    | some bs => if bits (BitArith.val bs) = bs then some (BitArith.val bs) else none) = some m
  rw [blBits?_bl]
  simp [val_bits]

/-- **The fire check is sound**: on a term it accepts, the jetted term
    reduces to the encoded outcome on the sample it read. -/
theorem hoon_dec_fires_sound {t : Term} {m : Nat} (e : hoonDecSample? t = some m) :
    WSteps (jetT hoonDecBodyF ⬝ t) (encOut (hoonDecOutN m)) := by
  obtain ⟨B, C, rfl⟩ := hoonDecSample?_sound e
  cases m with
  | zero => exact hoon_dec_free_zero B C
  | succ n => exact hoon_dec_free B C n

/-- **`HoonDecFires` is sound**: the fire check implies the reduction. -/
theorem hoon_dec_fires {t : Term} (h : HoonDecFires t) :
    ∃ m, hoonDecSample? t = some m ∧ m < 2 ^ 32 ∧
      WSteps (jetT hoonDecBodyF ⬝ t) (encOut (hoonDecOutN m)) :=
  let ⟨m, e, hm⟩ := h
  ⟨m, e, hm, hoon_dec_fires_sound e⟩

/-- The check, pinned by kernel evaluation: it fires on a canonical sample
    whatever the other fields, and declines at `2^32`, on a non-canonical
    bit list (`[1 0]`, a trailing `false`) and on a cell sample. -/
theorem hoonDecFires_pins :
    HoonDecFires (cellT S (cellT (aT 5) K)) ∧
    ¬ HoonDecFires (cellT S (cellT (aT (2 ^ 32)) K)) ∧
    ¬ HoonDecFires (cellT S (cellT (atomT (BitArith.bl [true, false])) K)) ∧
    ¬ HoonDecFires (cellT S (cellT (cellT K K) K)) := by decide +kernel

end Nock2Ski
