import Ski.AirProbe
import Ski.Converse
import Ski.Realize
import Nock2Ski.Value

open Term Probe
open BitArith (consO pairO nilT consT bl)

/-!
# The probe tree of a noun, and what the probe circuit certifies (M4f)

lean-ski reads a value by probing (`Ski/Decode.lean`, `Ski/ProbeTree.lean`):
the term applied to one fresh marker per constructor of its type
head-reduces to the marker of the constructor it is, applied to its
fields, which are read the same way.  `Probe.V` is the tree of such a
reading, `node c k ch`: the `c`-th of `k` constructors with fields `ch`;
`Probe.DecV t v` says `t` reads as `v` at every fresh base; `Air.planOf v
b0` lays the tree out as probe segments, and `Air.air_probe_sound` says a
table the AIR with probe segments accepts for that plan proves `DecV t.toO
v`.  All of that is generic in `V`.  What is SKIlark's is only `Probe.toV`,
the tree of a SKIlark `Outcome`, used by `air_probe_decodes` and by the
tooling (`bench/Jets.lean`'s `plan` and `check-probe`, which take an
outcome `err | val n…`; ski-air's `probe.rs::lean_plan`, which asks `lake
exe jets plan OUTCOME` for the plan; `bench/Circuit.lean`'s
`compare-probe`).

This module gives the tree of **our** encoding (`Nock2Ski/Noun.lean`):

    noun === Atom bits | Cell noun noun | Form noun noun code | Err     (4 markers)
    bits === Nil | Cons bit bits                                      (2 markers)
    bit  === T | F                                                    (2 markers)

`nounV p` is the tree of `encNoun p`: an atom is constructor `0` of `4`
with one field, the bits; a cell constructor `1` with two.  A product's
term may also be a `Form` (constructor `2`, three fields, the third its
compiled code), which no finite tree reads, since the code is a function
and probing it runs the formula on markers; so the plan is for the
code-free shape, which every atom has (`Enc.atom_inv`), and a cell product
has when its term is a `Cell` (`probe_complete`: `WSteps t (encNoun p)`).

**The theorems.**
- `decV_encNoun : DecV (encNoun p).toO (nounV p)`, completeness of the
  tree, from eight kernel-checked head reductions (`atom_hnf`, …), one per
  constructor applied to its markers.
- `encS_unique`: if `f` weakly reduces to a term of the shape of an
  encoding of `q` and reads as `nounV p`, then `q = p`; `err_unique`: it
  does not weakly reduce to `Err`.  By determinism of head reduction
  (`osteps_neutral_det`): both probes head-reduce to variable-headed
  spines, which must be the same spine.  No confluence is needed.
- `probe_value : DecV t.toO (nounV p) → ValueIs t p`: `t` has a weak head
  normal form (the probe closed at `S` converges, and `Converges.app_left`
  four times), and the two uniqueness lemmas say what it is.
- `probe_sound`: `Air.AcceptsP` for `planOf (nounV p) b0` with licensed
  roots gives `ValueIs t p`, by `air_probe_sound`; `probe_check`: the same
  of `Air.checkPA`, the checker over arrays (`lake exe nockprobe check`).

`ValueIs` is the hand-off to `Nock2Ski/Probe.lean`, which cannot be
imported here (it needs `NockEval`; see `Nock2Ski/Value.lean`).
-/

set_option linter.unusedSectionVars false

namespace Nock2Ski

variable [Kit]

-- ---------------------------------------------------------------------------
-- The probe tree of a noun
-- ---------------------------------------------------------------------------

/-- `bit === T | F`: `T` is constructor `0`, `F` constructor `1`. -/
def bitV : Bool → V
  | true => .node 0 2 []
  | false => .node 1 2 []

/-- `bits === Nil | Cons bit bits`, least significant first. -/
def bitsV : List Bool → V
  | [] => .node 0 2 []
  | b :: r => .node 1 2 [bitV b, bitsV r]

/-- **The probe tree of `encNoun p`**: `Atom` is constructor `0` of `4` with
    the bits as its field, `Cell` constructor `1` with two. -/
def nounV : Noun → V
  | .atom n => .node 0 4 [bitsV (bits n)]
  | .cell h t => .node 1 4 [nounV h, nounV t]

/-- The tree of the crash `Err`: constructor `3`, no fields. -/
def errV : V := .node 3 4 []

/-- **The plan of a product**: the segments of `nounV p`, markers from `0`,
    what the prover's PLAN table holds (`Air.planOf`). -/
def nounPlan (p : Noun) : List Air.Seg := Air.planOf (nounV p) 0

-- ---------------------------------------------------------------------------
-- Head reduction, computed
-- ---------------------------------------------------------------------------

/-- Head reduction with fuel, by lean-ski's `ostep?`. -/
def ohnf : Nat → OTerm → OTerm
  | 0, t => t
  | n + 1, t =>
    match ostep? t with
    | some u => ohnf n u
    | none => t

theorem ohnf_sound : ∀ (n : Nat) (t : OTerm), OSteps t (ohnf n t)
  | 0, t => .refl t
  | n + 1, t => by
    simp only [ohnf]
    split
    · rename_i u hu
      exact .step (ostep?_sound hu) (ohnf_sound n u)
    · exact .refl _

/-- The variables `0, 1, …` as the terms of `l`, the rest themselves. -/
def envO (l : List OTerm) : Nat → OTerm := fun i => (l[i]?).getD (.var i)

/-- The eight constructors applied to their markers (`0 … k - 1`, the
    fields the variables from `4`): each head-reduces to its marker applied
    to its fields, thunked as `K field marker`. -/
theorem atom_hnf : ohnf 40 (atomO (.var 4) ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3) =
    .var 0 ⬝ₒ (.K ⬝ₒ .var 4 ⬝ₒ .var 0) := by decide +kernel
theorem cell_hnf : ohnf 40 (cellO (.var 4) (.var 5) ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3) =
    .var 1 ⬝ₒ (.K ⬝ₒ .var 4 ⬝ₒ .var 1) ⬝ₒ (.K ⬝ₒ .var 5 ⬝ₒ .var 1) := by decide +kernel
theorem form_hnf :
    ohnf 40 (formO (.var 4) (.var 5) (.var 6) ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3) =
    .var 2 ⬝ₒ (.K ⬝ₒ .var 4 ⬝ₒ .var 2) ⬝ₒ (.K ⬝ₒ .var 5 ⬝ₒ .var 2) ⬝ₒ (.K ⬝ₒ .var 6 ⬝ₒ .var 2) := by
  decide +kernel
theorem err_hnf : ohnf 40 (errO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3) = .var 3 := by
  decide +kernel
theorem nil_hnf : ohnf 40 (.K ⬝ₒ .var 0 ⬝ₒ .var 1) = .var 0 := by decide +kernel
theorem cons_hnf : ohnf 40 (consO (.var 4) (.var 5) ⬝ₒ .var 0 ⬝ₒ .var 1) =
    .var 1 ⬝ₒ (.K ⬝ₒ .var 4 ⬝ₒ .var 1) ⬝ₒ (.K ⬝ₒ .var 5 ⬝ₒ .var 1) := by decide +kernel
theorem ff_hnf : ohnf 40 (.K ⬝ₒ .I ⬝ₒ .var 0 ⬝ₒ .var 1) = .var 1 := by decide +kernel

-- ---------------------------------------------------------------------------
-- The probes of the constructors, at any base
-- ---------------------------------------------------------------------------

/-- A probe of a closed term at base `0`, moved to base `β`. -/
theorem probe_base {t : Term} {k : Nat} {E : OTerm} (h : OSteps (appO t.toO (vars 0) k) E)
    (β : Nat) : OSteps (appO t.toO (vars β) k) (E.subst (shiftAt OTerm.var 0 β)) := by
  have := probe_subst OTerm.var β (fresh_toO t 0) h
  rwa [subst_var] at this

theorem shift_var (β j : Nat) : shiftAt OTerm.var 0 β j = .var (j + β) := by
  simp [shiftAt]

/-- `K x k ↠ x`, inside a field. -/
theorem thunk (x k : OTerm) : OWSteps (.K ⬝ₒ x ⬝ₒ k) x := (OSteps.single (.K x k)).weak

theorem probe_atom (b : Term) (β : Nat) :
    OWSteps (appO (atomT b).toO (vars β) 4) (appL (.var (0 + β)) [b.toO]) := by
  have h0 : OSteps (appO (atomT b).toO (vars 0) 4) (.var 0 ⬝ₒ (.K ⬝ₒ b.toO ⬝ₒ .var 0)) := by
    have h := (ohnf_sound 40 (atomO (.var 4) ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3)).subst
      (envO [.var 0, .var 1, .var 2, .var 3, b.toO])
    rw [atom_hnf] at h
    exact h
  have h := probe_base h0 β
  simp only [OTerm.subst, subst_toO, shift_var] at h
  exact h.weak.trans (OWSteps.right _ (thunk _ _))

theorem probe_cell (h t : Term) (β : Nat) :
    OWSteps (appO (cellT h t).toO (vars β) 4) (appL (.var (1 + β)) [h.toO, t.toO]) := by
  have h0 : OSteps (appO (cellT h t).toO (vars 0) 4)
      (.var 1 ⬝ₒ (.K ⬝ₒ h.toO ⬝ₒ .var 1) ⬝ₒ (.K ⬝ₒ t.toO ⬝ₒ .var 1)) := by
    have e := (ohnf_sound 40 (cellO (.var 4) (.var 5) ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3)).subst
      (envO [.var 0, .var 1, .var 2, .var 3, h.toO, t.toO])
    rw [cell_hnf] at e
    exact e
  have e := probe_base h0 β
  simp only [OTerm.subst, subst_toO, shift_var] at e
  exact e.weak.trans ((OWSteps.left _ (OWSteps.right _ (thunk _ _))).trans
    (OWSteps.right _ (thunk _ _)))

theorem probe_form (h t k : Term) (β : Nat) :
    OWSteps (appO (formT h t k).toO (vars β) 4) (appL (.var (2 + β)) [h.toO, t.toO, k.toO]) := by
  have h0 : OSteps (appO (formT h t k).toO (vars 0) 4)
      (.var 2 ⬝ₒ (.K ⬝ₒ h.toO ⬝ₒ .var 2) ⬝ₒ (.K ⬝ₒ t.toO ⬝ₒ .var 2) ⬝ₒ (.K ⬝ₒ k.toO ⬝ₒ .var 2)) := by
    have e := (ohnf_sound 40
      (formO (.var 4) (.var 5) (.var 6) ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3)).subst
      (envO [.var 0, .var 1, .var 2, .var 3, h.toO, t.toO, k.toO])
    rw [form_hnf] at e
    exact e
  have e := probe_base h0 β
  simp only [OTerm.subst, subst_toO, shift_var] at e
  exact e.weak.trans ((OWSteps.left _ (OWSteps.left _ (OWSteps.right _ (thunk _ _)))).trans
    ((OWSteps.left _ (OWSteps.right _ (thunk _ _))).trans (OWSteps.right _ (thunk _ _))))

theorem probe_err (β : Nat) : OSteps (appO errT.toO (vars β) 4) (appL (.var (3 + β)) []) := by
  have h0 : OSteps (appO errT.toO (vars 0) 4) (.var 3) := by
    have e := (ohnf_sound 40 (errO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2 ⬝ₒ .var 3)).subst
      (envO [.var 0, .var 1, .var 2, .var 3])
    rw [err_hnf] at e
    exact e
  have e := probe_base h0 β
  simp only [OTerm.subst, shift_var] at e
  exact e

theorem probe_nil (β : Nat) : OSteps (appO nilT.toO (vars β) 2) (appL (.var (0 + β)) []) := by
  have h0 : OSteps (appO nilT.toO (vars 0) 2) (.var 0) := by
    have e := (ohnf_sound 40 (.K ⬝ₒ .var 0 ⬝ₒ .var 1)).subst (envO [.var 0, .var 1])
    rw [nil_hnf] at e
    exact e
  have e := probe_base h0 β
  simp only [OTerm.subst, shift_var] at e
  exact e

theorem probe_cons (h t : Term) (β : Nat) :
    OWSteps (appO (consT h t).toO (vars β) 2) (appL (.var (1 + β)) [h.toO, t.toO]) := by
  have h0 : OSteps (appO (consT h t).toO (vars 0) 2)
      (.var 1 ⬝ₒ (.K ⬝ₒ h.toO ⬝ₒ .var 1) ⬝ₒ (.K ⬝ₒ t.toO ⬝ₒ .var 1)) := by
    have e := (ohnf_sound 40 (consO (.var 4) (.var 5) ⬝ₒ .var 0 ⬝ₒ .var 1)).subst
      (envO [.var 0, .var 1, .var 2, .var 3, h.toO, t.toO])
    rw [cons_hnf] at e
    exact e
  have e := probe_base h0 β
  simp only [OTerm.subst, subst_toO, shift_var] at e
  exact e.weak.trans ((OWSteps.left _ (OWSteps.right _ (thunk _ _))).trans
    (OWSteps.right _ (thunk _ _)))

theorem probe_tt (β : Nat) : OSteps (appO (Compose.boolT true).toO (vars β) 2) (appL (.var (0 + β)) []) :=
  probe_nil β

theorem probe_ff (β : Nat) : OSteps (appO (Compose.boolT false).toO (vars β) 2) (appL (.var (1 + β)) []) := by
  have h0 : OSteps (appO (Compose.boolT false).toO (vars 0) 2) (.var 1) := by
    have e := (ohnf_sound 40 (.K ⬝ₒ .I ⬝ₒ .var 0 ⬝ₒ .var 1)).subst (envO [.var 0, .var 1])
    rw [ff_hnf] at e
    exact e
  have e := probe_base h0 β
  simp only [OTerm.subst, shift_var] at e
  exact e

-- ---------------------------------------------------------------------------
-- Completeness: the encoding reads as its tree
-- ---------------------------------------------------------------------------

/-- A weak reduction to a spine is a reading of the spine's tree, when the
    fields read. -/
theorem decV_of_spine {t : OTerm} {c k : Nat} {fs : List OTerm} {ch : List V}
    (hb : Fresh 0 t) (h : OWSteps (appO t (vars 0) k) (appL (.var c) fs)) (hd : DecVs fs ch) :
    DecV t (.node c k ch) := by
  obtain ⟨fs', hs, hall⟩ := owsteps_spine h
  exact DecV.of_probe (c := c) (b0 := 0) hb hs (DecVs.of_allw hall hd)

theorem decV_bit : ∀ b : Bool, DecV (Compose.boolT b).toO (bitV b)
  | true => DecV.of_probe (c := 0) (b0 := 0) (fs := []) (fresh_toO _ 0) (probe_tt 0) trivial
  | false => DecV.of_probe (c := 1) (b0 := 0) (fs := []) (fresh_toO _ 0) (probe_ff 0) trivial

theorem decV_bits : ∀ l : List Bool, DecV (bl l).toO (bitsV l)
  | [] => DecV.of_probe (c := 0) (b0 := 0) (fs := []) (fresh_toO _ 0) (probe_nil 0) trivial
  | b :: r =>
    decV_of_spine (c := 1) (fs := [(Compose.boolT b).toO, (bl r).toO]) (fresh_toO _ 0)
      (probe_cons (Compose.boolT b) (bl r) 0) ⟨decV_bit b, decV_bits r, trivial⟩

/-- **Completeness**: `encNoun p` reads as `nounV p`. -/
theorem decV_encNoun : ∀ p : Noun, DecV (encNoun p).toO (nounV p)
  | .atom n =>
    decV_of_spine (c := 0) (fs := [(bl (bits n)).toO]) (fresh_toO _ 0)
      (probe_atom (bl (bits n)) 0) ⟨decV_bits (bits n), trivial⟩
  | .cell h t =>
    decV_of_spine (c := 1) (fs := [(encNoun h).toO, (encNoun t).toO]) (fresh_toO _ 0)
      (probe_cell (encNoun h) (encNoun t) 0) ⟨decV_encNoun h, decV_encNoun t, trivial⟩

/-- A term that weakly reduces to the code-free encoding reads as its tree:
    the prover can make the table (`DecV.of_owsteps`). -/
theorem probe_complete {t : Term} {p : Noun} (h : WSteps t (encNoun p)) : DecV t.toO (nounV p) :=
  DecV.of_owsteps h.toO (decV_encNoun p)

-- ---------------------------------------------------------------------------
-- Uniqueness: a reading is of one noun, by determinism of head reduction
-- ---------------------------------------------------------------------------

theorem appL_neutral : ∀ (fs : List OTerm) {t : OTerm}, ONeutral t → ONeutral (appL t fs)
  | [], _, h => h
  | _ :: fs, _, h => appL_neutral fs (.app _ h)

/-- Two head reductions of one probe to variable-headed spines reach the
    same spine. -/
theorem spine_det {t : OTerm} {c c' : Nat} {fs fs' : List OTerm}
    (h : OSteps t (appL (.var c) fs)) (h' : OSteps t (appL (.var c') fs')) :
    appL (.var c) fs = appL (.var c') fs' :=
  osteps_neutral_det h (appL_neutral fs (.var c)) h' (appL_neutral fs' (.var c'))

/-- A probe of `f` that weakly reduces to the spine `var c ⬝ fs`, against a
    head reduction of the same probe to a spine: that spine is `var c`
    applied to fields that weakly reduce to `fs`. -/
theorem reading_spine {f : OTerm} {b k c c' : Nat} {fs fs' : List OTerm}
    (h : OWSteps (appO f (vars b) k) (appL (.var c) fs))
    (h' : OSteps (appO f (vars b) k) (appL (.var c') fs')) :
    ∃ gs, appL (.var c) gs = appL (.var c') fs' ∧ AllW gs fs := by
  obtain ⟨gs, hs, hall⟩ := owsteps_spine h
  exact ⟨gs, spine_det hs h', hall⟩

-- Equal spines: the same constructor and the same fields, or no spine.
theorem spine0_eq {c c' : Nat} (e : appL (.var c) [] = appL (.var c') []) : c = c' :=
  OTerm.var.inj e
theorem spine1_eq {c c' : Nat} {a b : OTerm} (e : appL (.var c) [a] = appL (.var c') [b]) :
    c = c' ∧ a = b := by
  simp only [appL] at e
  injection e with e1 e2
  exact ⟨OTerm.var.inj e1, e2⟩
theorem spine2_eq {c c' : Nat} {a b a' b' : OTerm}
    (e : appL (.var c) [a, b] = appL (.var c') [a', b']) : c = c' ∧ a = a' ∧ b = b' := by
  simp only [appL] at e
  injection e with e1 e2
  injection e1 with e1 e3
  exact ⟨OTerm.var.inj e1, e3, e2⟩
theorem spine10 {c c' : Nat} {a : OTerm} (e : appL (.var c) [a] = appL (.var c') []) : False := by
  simp only [appL] at e; cases e
theorem spine20 {c c' : Nat} {a b : OTerm} (e : appL (.var c) [a, b] = appL (.var c') []) :
    False := by
  simp only [appL] at e; cases e
theorem spine21 {c c' : Nat} {a b a' : OTerm} (e : appL (.var c) [a, b] = appL (.var c') [a']) :
    False := by
  simp only [appL] at e; injection e with e1 e2; cases e1
theorem spine31 {c c' : Nat} {a b d a' : OTerm}
    (e : appL (.var c) [a, b, d] = appL (.var c') [a']) : False := by
  simp only [appL] at e; injection e with e1 e2; cases e1
theorem spine32 {c c' : Nat} {a b d a' b' : OTerm}
    (e : appL (.var c) [a, b, d] = appL (.var c') [a', b']) : False := by
  simp only [appL] at e; injection e with e1 e2; injection e1 with e1 e3; cases e1
theorem spine12 {c c' : Nat} {a a' b' : OTerm} (e : appL (.var c) [a] = appL (.var c') [a', b']) :
    False := by
  simp only [appL] at e; injection e with e1 e2; cases e1
theorem spine01 {c c' : Nat} {a : OTerm} (e : appL (.var c) [] = appL (.var c') [a]) : False := by
  simp only [appL] at e; cases e
theorem spine02 {c c' : Nat} {a b : OTerm} (e : appL (.var c) [] = appL (.var c') [a, b]) :
    False := by
  simp only [appL] at e; cases e

theorem bit_unique {g : OTerm} : ∀ {x x' : Bool}, OWSteps g (Compose.boolT x).toO →
    DecV g (bitV x') → x = x'
  | true, true, _, _ => rfl
  | false, false, _, _ => rfl
  | true, false, hg, hd => by
    obtain ⟨b, hb⟩ := fresh_exists g
    obtain ⟨fs', hs', hd'⟩ := hd b hb
    cases fs' with
    | cons _ _ => exact hd'.elim
    | nil =>
      obtain ⟨gs, e, hall⟩ := reading_spine (fs := [])
        ((OWSteps.appO (vars b) hg 2).trans (probe_tt b).weak) hs'
      cases hall
      have := spine0_eq e
      omega
  | false, true, hg, hd => by
    obtain ⟨b, hb⟩ := fresh_exists g
    obtain ⟨fs', hs', hd'⟩ := hd b hb
    cases fs' with
    | cons _ _ => exact hd'.elim
    | nil =>
      obtain ⟨gs, e, hall⟩ := reading_spine (fs := [])
        ((OWSteps.appO (vars b) hg 2).trans (probe_ff b).weak) hs'
      cases hall
      have := spine0_eq e
      omega

theorem bits_unique : ∀ (l : List Bool) {g : OTerm} {l' : List Bool},
    OWSteps g (bl l).toO → DecV g (bitsV l') → l = l'
  | [], g, [], _, _ => rfl
  | [], g, x' :: r', hg, hd => by
    have hg : OWSteps g nilT.toO := hg
    obtain ⟨b, hb⟩ := fresh_exists g
    obtain ⟨fs', hs', hd'⟩ := hd b hb
    match fs', hd' with
    | [g1, g2], _ =>
      obtain ⟨gs, e, hall⟩ := reading_spine (fs := [])
        ((OWSteps.appO (vars b) hg 2).trans (probe_nil b).weak) hs'
      cases hall
      exact (spine02 e).elim
  | x :: r, g, [], hg, hd => by
    have hg : OWSteps g (consT (Compose.boolT x) (bl r)).toO := hg
    obtain ⟨b, hb⟩ := fresh_exists g
    obtain ⟨fs', hs', hd'⟩ := hd b hb
    cases fs' with
    | cons _ _ => exact hd'.elim
    | nil =>
      obtain ⟨gs, e, hall⟩ := reading_spine
        ((OWSteps.appO (vars b) hg 2).trans (probe_cons (Compose.boolT x) (bl r) b)) hs'
      rcases hall with _ | ⟨_, _ | ⟨_, _ | _⟩⟩
      exact (spine20 e).elim
  | x :: r, g, x' :: r', hg, hd => by
    have hg : OWSteps g (consT (Compose.boolT x) (bl r)).toO := hg
    obtain ⟨b, hb⟩ := fresh_exists g
    obtain ⟨fs', hs', hd'⟩ := hd b hb
    match fs', hd' with
    | [g1, g2], ⟨hd1, hd2, _⟩ =>
      obtain ⟨gs, e, hall⟩ := reading_spine
        ((OWSteps.appO (vars b) hg 2).trans (probe_cons (Compose.boolT x) (bl r) b)) hs'
      rcases hall with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
      obtain ⟨_, e1, e2⟩ := spine2_eq e
      subst e1 e2
      rw [bit_unique h1 hd1, bits_unique r h2 hd2]

/-- **Uniqueness**: a term that weakly reduces to a term of the shape of an
    encoding of `q` and reads as `nounV p` has `q = p`. -/
theorem encS_unique : ∀ {q : Noun} {ep : Term}, EncS q ep → ∀ {f : OTerm} {p : Noun},
    OWSteps f ep.toO → DecV f (nounV p) → q = p := by
  intro q ep hq
  induction hq with
  | atom n =>
    intro f p hf hd
    obtain ⟨b, hb⟩ := fresh_exists f
    have hp := (OWSteps.appO (vars b) hf 4).trans (probe_atom (bl (bits n)) b)
    cases p with
    | atom m =>
      obtain ⟨fs', hs', hd'⟩ := hd b hb
      match fs', hd' with
      | [g], ⟨hg, _⟩ =>
        obtain ⟨gs, e, hall⟩ := reading_spine hp hs'
        rcases hall with _ | ⟨h1, _ | _⟩
        obtain ⟨_, e1⟩ := spine1_eq e
        subst e1
        exact congrArg Noun.atom (bits_inj (bits_unique (bits n) h1 hg))
    | cell h t =>
      obtain ⟨fs', hs', hd'⟩ := hd b hb
      match fs', hd' with
      | [g1, g2], _ =>
        obtain ⟨gs, e, hall⟩ := reading_spine hp hs'
        rcases hall with _ | ⟨_, _ | _⟩
        exact (spine12 e).elim
  | cell _ _ ihh iht =>
    intro f p hf hd
    obtain ⟨b, hb⟩ := fresh_exists f
    have hp := (OWSteps.appO (vars b) hf 4).trans (probe_cell _ _ b)
    cases p with
    | atom m =>
      obtain ⟨fs', hs', hd'⟩ := hd b hb
      match fs', hd' with
      | [g], _ =>
        obtain ⟨gs, e, hall⟩ := reading_spine hp hs'
        rcases hall with _ | ⟨_, _ | ⟨_, _ | _⟩⟩
        exact (spine21 e).elim
    | cell h' t' =>
      obtain ⟨fs', hs', hd'⟩ := hd b hb
      match fs', hd' with
      | [g1, g2], ⟨hd1, hd2, _⟩ =>
        obtain ⟨gs, e, hall⟩ := reading_spine hp hs'
        rcases hall with _ | ⟨h1, _ | ⟨h2, _ | _⟩⟩
        obtain ⟨_, e1, e2⟩ := spine2_eq e
        subst e1 e2
        rw [ihh h1 hd1, iht h2 hd2]
  | form k _ _ _ _ =>
    intro f p hf hd
    obtain ⟨b, hb⟩ := fresh_exists f
    have hp := (OWSteps.appO (vars b) hf 4).trans (probe_form _ _ k b)
    cases p with
    | atom m =>
      obtain ⟨fs', hs', hd'⟩ := hd b hb
      match fs', hd' with
      | [g], _ =>
        obtain ⟨gs, e, hall⟩ := reading_spine hp hs'
        rcases hall with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩
        exact (spine31 e).elim
    | cell h' t' =>
      obtain ⟨fs', hs', hd'⟩ := hd b hb
      match fs', hd' with
      | [g1, g2], _ =>
        obtain ⟨gs, e, hall⟩ := reading_spine hp hs'
        rcases hall with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩
        exact (spine32 e).elim

/-- A term that reads as a noun does not weakly reduce to the crash. -/
theorem err_unique {f : OTerm} {p : Noun} (hf : OWSteps f errT.toO) (hd : DecV f (nounV p)) :
    False := by
  obtain ⟨b, hb⟩ := fresh_exists f
  have hp := (OWSteps.appO (vars b) hf 4).trans (probe_err b).weak
  cases p with
  | atom m =>
    obtain ⟨fs', hs', hd'⟩ := hd b hb
    match fs', hd' with
    | [g], _ =>
      obtain ⟨gs, e, hall⟩ := reading_spine (fs := []) hp hs'
      cases hall
      exact spine01 e
  | cell h' t' =>
    obtain ⟨fs', hs', hd'⟩ := hd b hb
    match fs', hd' with
    | [g1, g2], _ =>
      obtain ⟨gs, e, hall⟩ := reading_spine (fs := []) hp hs'
      cases hall
      exact spine02 e

-- ---------------------------------------------------------------------------
-- The value, read
-- ---------------------------------------------------------------------------

/-- A term that reads as a noun converges: its probe closed at `S` reaches
    `S` applied to one or two fields, a weak head normal form. -/
theorem converges_of_decV {t : Term} {p : Noun} (h : DecV t.toO (nounV p)) : Converges t := by
  have e : appF t (fun i => (vars 0 i).close fun _ => S) 4 = t ⬝ S ⬝ S ⬝ S ⬝ S := rfl
  suffices hc : Converges (t ⬝ S ⬝ S ⬝ S ⬝ S) from
    Converges.app_left (Converges.app_left (Converges.app_left (Converges.app_left hc)))
  cases p with
  | atom n =>
    obtain ⟨fs, hs, hd⟩ := h 0 (fresh_toO t 0)
    match fs, hd with
    | [f], _ =>
      have hc := hs.close (fun _ => S)
      rw [close_appO, close_toO, e] at hc
      exact ⟨_, hc, .S1 _⟩
  | cell a b =>
    obtain ⟨fs, hs, hd⟩ := h 0 (fresh_toO t 0)
    match fs, hd with
    | [f, g], _ =>
      have hc := hs.close (fun _ => S)
      rw [close_appO, close_toO, e] at hc
      exact ⟨_, hc, .S2 _ _⟩

/-- **A reading is the value**: a term that reads as `nounV p` has `p` as
    its value. -/
theorem probe_value {t : Term} {p : Noun} (h : DecV t.toO (nounV p)) : ValueIs t p := by
  obtain ⟨v, hv⟩ := converges_of_decV h
  refine ⟨v, hv, fun herr => ?_, fun q ep hq hw => ?_⟩
  · exact err_unique (hv.1.weak.trans herr).toO h
  · exact encS_unique hq (hv.1.weak.trans hw).toO h

-- ---------------------------------------------------------------------------
-- The circuit
-- ---------------------------------------------------------------------------

/-- **The AIR with probe segments, for a noun** (lean-ski's
    `Air.air_probe_sound` at `nounV p`): a table it accepts for the plan of
    `p`, from a loaded term whose roots are licensed, proves that the
    term's value is `p`. -/
theorem probe_sound {M : List Cell} {t : Term} {roots : List (Nat × Nat)}
    {jets : List Air.Jet} {P : Nat → Nat} {fld : Nat → List Nat} {row : Nat → Air.Row}
    {p : Noun} {b0 : Nat}
    (h : Air.AcceptsP M (Mach.load t) roots jets (Air.planOf (nounV p) b0) P fld row)
    (hroots : Air.RootsOK (Mach.load t).heap roots jets) : ValueIs t p :=
  probe_value (Air.air_probe_sound h hroots)

/-- **The checker** (`Air.checkPA`, `lake exe nockprobe check`): a table it
    accepts for `nounPlan p` proves that the term's value is `p`. -/
theorem probe_check {A : Array Cell} {t : Term} {roots : List (Nat × Nat)}
    {jets : List Air.Jet} {starts : Array Nat} {flds : Array (List Nat)} {R : Array Air.Row}
    {p : Noun} (h : Air.checkPA A t roots jets (nounPlan p) starts flds R = true) : ValueIs t p :=
  let ⟨hr, ha⟩ := Air.checkPA_sound h
  probe_sound ha hr

end Nock2Ski
