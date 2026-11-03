import Nock2Ski.Compile

open Nock
open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

/-!
# The encoding relation, and the primitives over it

Milestone M2 of `PLAN.md`, §2.4.  lean-nock's `NockEval` runs on nouns
with no code; the runtime's values carry code on formula-shaped cells
(`Form`), put there by `encLit` for the literals of `[1 …]` and kept by
every projection.  A product's term is therefore not a function of the
noun: `[1 [0 1]]` returns a `Form`, `[[1 0] [1 1]]` a `Cell` of the same
noun.  The simulation is stated over a relation.

`Enc n e`: `e` encodes the noun `n`, an atom as `encNoun` does, a cell as
`Cell` of encodings of its halves or as `Form` of them with **its own
compiled code** `nockToSki n`.  Both `encNoun n` (no code, the hidden
subject of the statement path) and `encLit n` (the runtime's literal, code
on every formula-shaped cell) are `Enc n`.  The code is `nockToSki n`
whatever the shape, so `app` on a `Form` runs exactly the compiled formula
of the noun it encodes (`app_enc`).

Every primitive spec of `Prims.lean` is restated here over `Enc`: the
symbolic runs there are over open constructor terms, so the `Cell` and
`Form` cases are the same runs closed with the encodings of the fields.
`eqn` needs five more runs for the `Form` combinations (`eqn_af_run`, …).

The second half relates lean-nock's `fasO` and `haxO`, recursive on the
axis, to walks along `axisPath n` (`fasO_axisPath`, `haxO_axisPath`), and
proves the tagged pull along a path over `Enc` (`pick_enc`,
`pick_enc_none`).
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- The relation
-- ---------------------------------------------------------------------------

/-- `e` encodes `n`: atoms as `encNoun`, a cell as a `Cell` or as a `Form`
    carrying its own compiled code. -/
inductive Enc : Noun → Term → Prop
  | atom (n : Nat) : Enc (.atom n) (encNoun (.atom n))
  | cell {h t : Noun} {eh et : Term} : Enc h eh → Enc t et → Enc (.cell h t) (cellT eh et)
  | form {h t : Noun} {eh et : Term} : Enc h eh → Enc t et →
      Enc (.cell h t) (formT eh et (nockToSki (.cell h t)))

/-- The code-free encoding is an encoding. -/
theorem enc_encNoun : ∀ n, Enc n (encNoun n)
  | .atom n => .atom n
  | .cell h t => .cell (enc_encNoun h) (enc_encNoun t)

/-- The runtime's literal is an encoding. -/
theorem enc_encLit : ∀ n, Enc n (encLit n)
  | .atom n => by rw [encLit]; exact .atom n
  | .cell h t => by
    rw [encLit]
    split
    · exact .form (enc_encLit h) (enc_encLit t)
    · exact .cell (enc_encLit h) (enc_encLit t)

theorem Enc.atom_inv {n : Nat} {e : Term} (h : Enc (.atom n) e) : e = encNoun (.atom n) := by
  cases h; rfl

theorem Enc.cell_inv {h t : Noun} {e : Term} (he : Enc (.cell h t) e) :
    ∃ eh et, Enc h eh ∧ Enc t et ∧ (e = cellT eh et ∨ e = formT eh et (nockToSki (.cell h t))) := by
  cases he with
  | cell hh ht => exact ⟨_, _, hh, ht, .inl rfl⟩
  | form hh ht => exact ⟨_, _, hh, ht, .inr rfl⟩

-- ---------------------------------------------------------------------------
-- The `Cell` runs of Prims.lean, closed with arbitrary fields
-- ---------------------------------------------------------------------------

theorem hd_cellT (h t : Term) : WSteps (hdT ⬝ cellT h t) h := by
  have e := run hd_cell_run (envR [K, h, t])
  simp only [OTerm.close, close_toO, close_cellO] at e
  exact e

theorem tl_cellT (h t : Term) : WSteps (tlT ⬝ cellT h t) t := by
  have e := run tl_cell_run (envR [K, h, t])
  simp only [OTerm.close, close_toO, close_cellO] at e
  exact e

theorem force_cellT (h t k : Term) : WSteps (forceT ⬝ cellT h t ⬝ k) (k ⬝ cellT h t) := by
  have e := run force_cell_run (envR [K, h, t, k])
  simp only [OTerm.close, close_toO, close_cellO] at e
  exact e

theorem cel_cellT (h t : Term) : WSteps (celT ⬝ cellT h t) (encNoun (.atom 0)) := by
  have e := run cel_cell_run (envR [K, h, t])
  simp only [OTerm.close, close_toO, close_cellO, close_atomO] at e
  rw [encNoun_atom, bits_zero]
  exact e

theorem inc_cellT (h t : Term) : WSteps (incT ⬝ cellT h t) errT := by
  have e := run inc_cell_run (envR [K, h, t])
  simp only [OTerm.close, close_cellO, close_errO] at e
  rw [incGO_close _ rfl] at e
  exact e

theorem ifn_cellT (h t y n : Term) : WSteps (ifnT ⬝ cellT h t ⬝ y ⬝ n) errT := by
  have e := run ifn_cell_run (envR [K, h, y, n, t])
  simp only [OTerm.close, close_toO, close_cellO, close_errO] at e
  exact e

-- ---------------------------------------------------------------------------
-- The primitives over `Enc`
-- ---------------------------------------------------------------------------

/-- `force` hands any encoding to its continuation. -/
theorem force_enc {n : Noun} {e : Term} (he : Enc n e) (k : Term) :
    WSteps (forceT ⬝ e ⬝ k) (k ⬝ e) := by
  cases he with
  | atom n => exact force_spec (.atom n) k
  | cell _ _ => exact force_cellT _ _ _
  | form _ _ => exact force_form _ _ _ _

/-- `hd` of an encoded cell is an encoding of its head. -/
theorem hd_enc {h t : Noun} {e : Term} (he : Enc (.cell h t) e) :
    ∃ eh, Enc h eh ∧ WSteps (hdT ⬝ e) eh := by
  cases he with
  | cell hh _ => exact ⟨_, hh, hd_cellT _ _⟩
  | form hh _ => exact ⟨_, hh, hd_form _ _ _⟩

theorem tl_enc {h t : Noun} {e : Term} (he : Enc (.cell h t) e) :
    ∃ et, Enc t et ∧ WSteps (tlT ⬝ e) et := by
  cases he with
  | cell _ ht => exact ⟨_, ht, tl_cellT _ _⟩
  | form _ ht => exact ⟨_, ht, tl_form _ _ _⟩

theorem hd_enc_atom {n : Nat} {e : Term} (he : Enc (.atom n) e) : WSteps (hdT ⬝ e) errT := by
  rw [he.atom_inv]; exact hd_atom n

theorem tl_enc_atom {n : Nat} {e : Term} (he : Enc (.atom n) e) : WSteps (tlT ⬝ e) errT := by
  rw [he.atom_inv]; exact tl_atom n

/-- `cel` is `wut` on any encoding. -/
theorem cel_enc {n : Noun} {e : Term} (he : Enc n e) : WSteps (celT ⬝ e) (encNoun (wut n)) := by
  cases he with
  | atom n => exact cel_spec (.atom n)
  | cell _ _ => exact cel_cellT _ _
  | form _ _ => exact cel_form _ _ _

/-- `inc` on an encoded atom is `lusO`. -/
theorem inc_enc_atom {n : Nat} {e : Term} (he : Enc (.atom n) e) :
    WSteps (incT ⬝ e) (encNoun (.atom (1 + n))) := by
  rw [he.atom_inv, Nat.add_comm]; exact inc_spec n

/-- `inc` crashes on an encoded cell. -/
theorem inc_enc_cell {h t : Noun} {e : Term} (he : Enc (.cell h t) e) : WSteps (incT ⬝ e) errT := by
  cases he with
  | cell _ _ => exact inc_cellT _ _
  | form _ _ => exact inc_form _ _ _

/-- `app` on an encoded cell runs its compiled code when it carries one,
    and otherwise hands the cell to the interpreter `nockI` (M3; M1's `app`
    crashed there). -/
theorem app_enc {h t : Noun} {e x : Term} (he : Enc (.cell h t) e) :
    WSteps (appT ⬝ e ⬝ x) (nockToSki (.cell h t) ⬝ x) ∨ WSteps (appT ⬝ e ⬝ x) (nockIT ⬝ x ⬝ e) := by
  cases he with
  | cell _ _ => exact .inr (app_cell _ _ _)
  | form _ _ => exact .inl (app_form _ _ _ _)

theorem app_enc_atom {n : Nat} {e x : Term} (he : Enc (.atom n) e) : WSteps (appT ⬝ e ⬝ x) errT := by
  rw [he.atom_inv]; exact app_atom _ x

/-- `ifn` on `0`, `1`, and anything else. -/
theorem ifn_enc_zero {e : Term} (he : Enc (.atom 0) e) (y n : Term) : WSteps (ifnT ⬝ e ⬝ y ⬝ n) y := by
  rw [he.atom_inv]; exact ifn_zero y n

theorem ifn_enc_one {e : Term} (he : Enc (.atom 1) e) (y n : Term) : WSteps (ifnT ⬝ e ⬝ y ⬝ n) n := by
  rw [he.atom_inv]; exact ifn_one y n

theorem ifn_enc_crash {r : Noun} {e : Term} (he : Enc r e) (h0 : r ≠ .atom 0) (h1 : r ≠ .atom 1)
    (y n : Term) : WSteps (ifnT ⬝ e ⬝ y ⬝ n) errT := by
  cases he with
  | atom m =>
    have hm : 2 ≤ m := by
      rcases m with _ | _ | m
      · exact absurd rfl h0
      · exact absurd rfl h1
      · omega
    exact ifn_big hm y n
  | cell _ _ => exact ifn_cellT _ _ _ _
  | form _ _ => exact ifn_form _ _ _ _ _

-- ---------------------------------------------------------------------------
-- eq over `Enc`: the `Form` combinations
-- ---------------------------------------------------------------------------

theorem eqn_af_run :
    wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ atomO (.var 11) ⬝ₒ formO (.var 12) (.var 13) (.var 14)) =
      .K ⬝ₒ .I := by decide +kernel
theorem eqn_fa_run :
    wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ formO (.var 11) (.var 12) (.var 15) ⬝ₒ atomO (.var 13)) =
      .K ⬝ₒ .I := by decide +kernel
theorem eqn_cf_run :
    wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ cellO (.var 11) (.var 12) ⬝ₒ formO (.var 13) (.var 14) (.var 15)) =
      .var 10 ⬝ₒ .var 11 ⬝ₒ .var 13 ⬝ₒ (.var 10 ⬝ₒ .var 12 ⬝ₒ .var 14) ⬝ₒ ffO := by
  decide +kernel
theorem eqn_fc_run :
    wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ formO (.var 11) (.var 12) (.var 15) ⬝ₒ cellO (.var 13) (.var 14)) =
      .var 10 ⬝ₒ .var 11 ⬝ₒ .var 13 ⬝ₒ (.var 10 ⬝ₒ .var 12 ⬝ₒ .var 14) ⬝ₒ ffO := by
  decide +kernel
theorem eqn_ff_run :
    wnf 200 (eqnGO ⬝ₒ .var 10 ⬝ₒ formO (.var 11) (.var 12) (.var 15) ⬝ₒ
        formO (.var 13) (.var 14) (.var 16)) =
      .var 10 ⬝ₒ .var 11 ⬝ₒ .var 13 ⬝ₒ (.var 10 ⬝ₒ .var 12 ⬝ₒ .var 14) ⬝ₒ ffO := by
  decide +kernel

/-- The two-cell step of `eqn`: compare the heads, and on `T` the tails. -/
private theorem eqn_cells {h t h2 t2 : Noun} {eh et eh2 et2 : Term}
    (ihh : WSteps (eqnFix ⬝ eh ⬝ eh2) (boolT (decide (h = h2))))
    (iht : WSteps (eqnFix ⬝ et ⬝ et2) (boolT (decide (t = t2)))) :
    WSteps (eqnFix ⬝ eh ⬝ eh2 ⬝ (eqnFix ⬝ et ⬝ et2) ⬝ (K ⬝ I))
      (boolT (decide (Noun.cell h t = Noun.cell h2 t2))) := by
  rw [show decide (Noun.cell h t = Noun.cell h2 t2) = (decide (h = h2) && decide (t = t2)) by simp]
  refine (WSteps.left _ (WSteps.left _ ihh)).trans ((Compose.boolT_sel _ _ _).trans ?_)
  cases decide (h = h2)
  · exact .refl _
  · exact iht

/-- **`eqn`** is structural equality on encodings, code ignored. -/
theorem eqn_enc : ∀ {a : Noun} {ea : Term}, Enc a ea → ∀ {b : Noun} {eb : Term}, Enc b eb →
    WSteps (eqnFix ⬝ ea ⬝ eb) (boolT (decide (a = b))) := by
  intro a ea ha
  induction ha with
  | atom m =>
    intro b eb hb
    cases hb with
    | atom n =>
      have e := run eqn_aa_run (envR [eqnFix, bitsT (bits m), bitsT (bits n)])
      simp only [OTerm.close, close_atomO] at e
      rw [eqnGO_close _ rfl] at e
      rw [show decide (Noun.atom m = Noun.atom n) = decide (bits m = bits n) by
        simp [bits_eq_iff]]
      exact (eqn_unfold _ _).trans (e.trans
        ((WSteps.left _ (WSteps.left _ (Ycomb_unroll eqbG))).trans (eqb_spec _ _)))
    | @cell h t eh et _ _ =>
      have e := run eqn_ac_run (envR [eqnFix, bitsT (bits m), eh, et])
      simp only [OTerm.close, close_atomO, close_cellO] at e
      rw [eqnGO_close _ rfl] at e
      rw [show decide (Noun.atom m = Noun.cell h t) = false by simp]
      exact (eqn_unfold _ _).trans e
    | @form h t eh et _ _ =>
      have e := run eqn_af_run (envR [eqnFix, bitsT (bits m), eh, et, nockToSki (.cell h t)])
      simp only [OTerm.close, close_atomO, close_formO] at e
      rw [eqnGO_close _ rfl] at e
      rw [show decide (Noun.atom m = Noun.cell h t) = false by simp]
      exact (eqn_unfold _ _).trans e
  | @cell h t eh et _ _ ihh iht =>
    intro b eb hb
    cases hb with
    | atom n =>
      have e := run eqn_ca_run (envR [eqnFix, eh, et, bitsT (bits n)])
      simp only [OTerm.close, close_atomO, close_cellO] at e
      rw [eqnGO_close _ rfl] at e
      rw [show decide (Noun.cell h t = Noun.atom n) = false by simp]
      exact (eqn_unfold _ _).trans e
    | @cell h2 t2 eh2 et2 hh2 ht2 =>
      have e := run eqn_cc_run (envR [eqnFix, eh, et, eh2, et2])
      simp only [OTerm.close, close_cellO, close_ffO] at e
      rw [eqnGO_close _ rfl] at e
      exact (eqn_unfold _ _).trans (e.trans (eqn_cells (ihh hh2) (iht ht2)))
    | @form h2 t2 eh2 et2 hh2 ht2 =>
      have e := run eqn_cf_run (envR [eqnFix, eh, et, eh2, et2, nockToSki (.cell h2 t2)])
      simp only [OTerm.close, close_cellO, close_formO, close_ffO] at e
      rw [eqnGO_close _ rfl] at e
      exact (eqn_unfold _ _).trans (e.trans (eqn_cells (ihh hh2) (iht ht2)))
  | @form h t eh et _ _ ihh iht =>
    intro b eb hb
    cases hb with
    | atom n =>
      have e := run eqn_fa_run (envR [eqnFix, eh, et, bitsT (bits n), K, nockToSki (.cell h t)])
      simp only [OTerm.close, close_atomO, close_formO] at e
      rw [eqnGO_close _ rfl] at e
      rw [show decide (Noun.cell h t = Noun.atom n) = false by simp]
      exact (eqn_unfold _ _).trans e
    | @cell h2 t2 eh2 et2 hh2 ht2 =>
      have e := run eqn_fc_run (envR [eqnFix, eh, et, eh2, et2, nockToSki (.cell h t)])
      simp only [OTerm.close, close_cellO, close_formO, close_ffO] at e
      rw [eqnGO_close _ rfl] at e
      exact (eqn_unfold _ _).trans (e.trans (eqn_cells (ihh hh2) (iht ht2)))
    | @form h2 t2 eh2 et2 hh2 ht2 =>
      have e := run eqn_ff_run
        (envR [eqnFix, eh, et, eh2, et2, nockToSki (.cell h t), nockToSki (.cell h2 t2)])
      simp only [OTerm.close, close_formO, close_ffO] at e
      rw [eqnGO_close _ rfl] at e
      exact (eqn_unfold _ _).trans (e.trans (eqn_cells (ihh hh2) (iht ht2)))

/-- **`eq`** is `tisN` on encodings. -/
theorem eq_enc {a b : Noun} {ea eb : Term} (ha : Enc a ea) (hb : Enc b eb) :
    WSteps (eqT ⬝ ea ⬝ eb) (encNoun (tisN a b)) := by
  have e := run eq_run (envR [K, ea, eb])
  simp only [OTerm.close] at e
  rw [eqGO_close _ rfl rfl] at e
  refine e.trans ((WSteps.right _ ((WSteps.left _ (WSteps.left _ (Ycomb_unroll eqnG))).trans
    (eqn_enc ha hb))).trans ?_)
  unfold tisN
  by_cases hab : a = b
  · rw [if_pos hab, decide_eq_true hab]; exact loob_spec true
  · rw [if_neg hab, decide_eq_false hab]; exact loob_spec false

-- ---------------------------------------------------------------------------
-- Paths: lean-nock's `fasO` and `haxO` along `axisPath`
-- ---------------------------------------------------------------------------

theorem slot_append : ∀ (bs cs : List Bool) (x : Noun),
    slot x (bs ++ cs) = (slot x bs).bind (fun y => slot y cs)
  | [], _, _ => rfl
  | false :: bs, cs, .cell l _ => slot_append bs cs l
  | true :: bs, cs, .cell _ r => slot_append bs cs r
  | false :: _, _, .atom _ => rfl
  | true :: _, _, .atom _ => rfl

theorem slot_atom (n : Nat) (b : Bool) (bs : List Bool) : slot (.atom n) (b :: bs) = none := by
  cases b <;> rfl

theorem fasO_cell (p q x : Noun) : fasO (.cell p q) x = none := by simp [fasO]

/-- `/[n x]` for `n ≥ 1` is the walk along `axisPath n`. -/
theorem fasO_axisPath : ∀ (n : Nat) (x : Noun), 1 ≤ n → fasO (.atom n) x = slot x (axisPath n)
  | 0, _, h => absurd h (by omega)
  | 1, x, _ => by rw [fasO_one, axisPath_one]; rfl
  | 2, x, _ => by
    rw [axisPath_rec (by omega), axisPath_one]
    cases x <;> simp [fasO, slot]
  | 3, x, _ => by
    rw [axisPath_rec (by omega), axisPath_one]
    cases x <;> simp [fasO, slot]
  | m + 4, x, _ => by
    rw [axisPath_rec (by omega), slot_append, ← fasO_axisPath ((m + 4) / 2) x (by omega), fasO]
    cases fasO (.atom ((m + 4) / 2)) x with
    | none => rfl
    | some y =>
      cases y with
      | atom a =>
        show none = slot (Noun.atom a) [(m + 4) % 2 == 1]
        rw [slot_atom]
      | cell hd tl =>
        show (if (m + 4) % 2 = 0 then some hd else some tl) = slot (Noun.cell hd tl) [(m + 4) % 2 == 1]
        by_cases hp : (m + 4) % 2 = 0
        · have hb : ((m + 4) % 2 == 1) = false := by simp [hp]
          rw [if_pos hp, hb]; rfl
        · have hb : ((m + 4) % 2 == 1) = true := by simp; omega
          rw [if_neg hp, hb]; rfl
termination_by n => n

/-- `#[n v t]` along a path from the root: `editP v bs t` is `t` with the
    subtree at `bs` replaced by `v`, `none` into an atom. -/
def editP (v : Noun) : List Bool → Noun → Option Noun
  | [], _ => some v
  | false :: bs, .cell l r => (editP v bs l).map (fun l' => .cell l' r)
  | true :: bs, .cell l r => (editP v bs r).map (fun r' => .cell l r')
  | _ :: _, .atom _ => none

theorem editP_append : ∀ (bs cs : List Bool) (v t : Noun),
    editP v (bs ++ cs) t = match slot t bs with
      | none => none
      | some sub => (editP v cs sub).bind (fun sub' => editP sub' bs t)
  | [], cs, v, t => by
    show editP v cs t = (editP v cs t).bind (fun sub' => some sub')
    cases editP v cs t <;> rfl
  | false :: _, _, _, .atom _ => rfl
  | true :: _, _, _, .atom _ => rfl
  | false :: bs, cs, v, .cell l r => by
    show (editP v (bs ++ cs) l).map (fun l' => Noun.cell l' r) = _
    rw [editP_append bs cs v l]
    show _ = match slot l bs with
      | none => none
      | some sub => (editP v cs sub).bind (fun sub' => (editP sub' bs l).map (fun l' => Noun.cell l' r))
    cases slot l bs with
    | none => rfl
    | some sub =>
      show Option.map (fun l' => Noun.cell l' r) ((editP v cs sub).bind (fun sub' => editP sub' bs l)) =
        (editP v cs sub).bind (fun sub' => (editP sub' bs l).map (fun l' => Noun.cell l' r))
      cases editP v cs sub <;> rfl
  | true :: bs, cs, v, .cell l r => by
    show (editP v (bs ++ cs) r).map (fun r' => Noun.cell l r') = _
    rw [editP_append bs cs v r]
    show _ = match slot r bs with
      | none => none
      | some sub => (editP v cs sub).bind (fun sub' => (editP sub' bs r).map (fun r' => Noun.cell l r'))
    cases slot r bs with
    | none => rfl
    | some sub =>
      show Option.map (fun r' => Noun.cell l r') ((editP v cs sub).bind (fun sub' => editP sub' bs r)) =
        (editP v cs sub).bind (fun sub' => (editP sub' bs r).map (fun r' => Noun.cell l r'))
      cases editP v cs sub <;> rfl

theorem editP_atom (v : Noun) (b : Bool) (bs : List Bool) (n : Nat) :
    editP v (b :: bs) (.atom n) = none := by
  cases b <;> rfl

theorem haxO_cell (p q v t : Noun) : haxO (.cell p q) v t = none := by simp [haxO]

/-- `#[n v t]` for `n ≥ 1` is the edit along `axisPath n`. -/
theorem haxO_axisPath : ∀ (n : Nat) (v t : Noun), 1 ≤ n → haxO (.atom n) v t = editP v (axisPath n) t
  | 0, _, _, h => absurd h (by omega)
  | 1, v, t, _ => by rw [haxO_one, axisPath_one]; rfl
  | m + 2, v, t, _ => by
    have ha : 1 ≤ (m + 2) / 2 := by omega
    have e1 : fasO (.atom ((m + 2) / 2 + (m + 2) / 2 + 1)) t =
        (slot t (axisPath ((m + 2) / 2))).bind (fun y => slot y [true]) := by
      rw [fasO_axisPath _ _ (by omega), axisPath_rec (by omega)]
      have h1 : ((m + 2) / 2 + (m + 2) / 2 + 1) / 2 = (m + 2) / 2 := by omega
      have h2 : ((m + 2) / 2 + (m + 2) / 2 + 1) % 2 = 1 := by omega
      rw [h1, h2, slot_append]; rfl
    have e2 : fasO (.atom ((m + 2) / 2 + (m + 2) / 2)) t =
        (slot t (axisPath ((m + 2) / 2))).bind (fun y => slot y [false]) := by
      rw [fasO_axisPath _ _ (by omega), axisPath_rec (by omega)]
      have h1 : ((m + 2) / 2 + (m + 2) / 2) / 2 = (m + 2) / 2 := by omega
      have h2 : ((m + 2) / 2 + (m + 2) / 2) % 2 = 0 := by omega
      rw [h1, h2, slot_append]; rfl
    rw [axisPath_rec (by omega), editP_append, haxO]
    simp only [e1, e2]
    cases slot t (axisPath ((m + 2) / 2)) with
    | none => split <;> rfl
    | some sub =>
      cases sub with
      | atom _ => split <;> simp [slot_atom, editP_atom]
      | cell l r =>
        by_cases hp : (m + 2) % 2 = 0
        · have hb : ((m + 2) % 2 == 1) = false := by simp [hp]
          rw [if_pos hp, hb]
          exact haxO_axisPath ((m + 2) / 2) (.cell v r) t ha
        · have hb : ((m + 2) % 2 == 1) = true := by simp; omega
          rw [if_neg hp, hb]
          exact haxO_axisPath ((m + 2) / 2) (.cell l v) t ha
termination_by n => n

-- ---------------------------------------------------------------------------
-- The tagged pull along a path, over `Enc`
-- ---------------------------------------------------------------------------

theorem pick_err : ∀ bs : List Bool, WSteps (pickT errT bs) errT
  | [] => .refl _
  | false :: bs => (pickT_cong hd_err bs).trans (pick_err bs)
  | true :: bs => (pickT_cong tl_err bs).trans (pick_err bs)

/-- Along a path the noun has, the pull of an encoding is an encoding of
    the subtree. -/
theorem pick_enc : ∀ (bs : List Bool) {x : Noun} {ex e : Term} (y : Noun),
    slot x bs = some y → Enc x ex → WSteps e ex → ∃ ey, Enc y ey ∧ WSteps (pickT e bs) ey
  | [], x, ex, e, y, h, hx, he => by
    obtain rfl : x = y := by simpa [slot] using h
    exact ⟨ex, hx, he⟩
  | false :: bs, .cell l r, ex, e, y, h, hx, he =>
    let ⟨el, hl, hhd⟩ := hd_enc hx
    pick_enc bs y h hl ((WSteps.right _ he).trans hhd)
  | true :: bs, .cell l r, ex, e, y, h, hx, he =>
    let ⟨er, hr, htl⟩ := tl_enc hx
    pick_enc bs y h hr ((WSteps.right _ he).trans htl)
  | _ :: _, .atom _, _, _, _, h, _, _ => by simp [slot] at h

/-- Along a path into an atom, the pull crashes. -/
theorem pick_enc_none : ∀ (bs : List Bool) {x : Noun} {ex e : Term},
    slot x bs = none → Enc x ex → WSteps e ex → WSteps (pickT e bs) errT
  | [], _, _, _, h, _, _ => by simp [slot] at h
  | false :: bs, .atom n, ex, e, _, hx, he =>
    (pickT_cong ((WSteps.right _ he).trans (hd_enc_atom hx)) bs).trans (pick_err bs)
  | true :: bs, .atom n, ex, e, _, hx, he =>
    (pickT_cong ((WSteps.right _ he).trans (tl_enc_atom hx)) bs).trans (pick_err bs)
  | false :: bs, .cell l r, ex, e, h, hx, he =>
    let ⟨el, hl, hhd⟩ := hd_enc hx
    pick_enc_none bs h hl ((WSteps.right _ he).trans hhd)
  | true :: bs, .cell l r, ex, e, h, hx, he =>
    let ⟨er, hr, htl⟩ := tl_enc hx
    pick_enc_none bs h hr ((WSteps.right _ he).trans htl)

end Nock2Ski
