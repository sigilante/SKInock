import Nock2Ski.Converse
import Nock2Ski.JetSpec
import Ski.DataJet

open Term DataJet

/-!
# Jet transport (M5, PLAN.md §3): a Nock jet's contract as a lean-ski data jet

lean-nock licenses a jet for a Λ word `w` by its leaf proof: the Nock
formula `phi w` evaluates on every subject `S` to the C model's outcome,
`cw w S`, a value or a crash (`leaf_correct`), and the model as a jet meets
the three-valued contract (`word_jet_sound`).  lean-ski licenses a data jet
by a `Contract` (`Ski/DataJet.lean`): a specification `spec : α → β` with
encodings `encI`, `encO`, implemented by a term `P` when `P ⬝ encI x ↠ encO
(spec x)` for every `x` (`Implements`); any implementation may then stand in
for the jet (`JSteps.close`, `real_of_jet`).

**Transport.**  For a formula `f` with a total model `c` (`Leaf f c : ∀ S,
NockEval S f (c S)`, `Nock2Ski/JetSpec.lean`):

- the contract `nounContract c` is `spec := c` over `α := Noun`, `β :=
  Outcome`, the input encoded by `encNoun`, a value by `encNoun`, the crash
  by `Err`;
- the implementation is `jetT f = λx. toCell (nockToSki f x)`: the compiled
  formula, its result copied code-free by `toCellT`;
- `jet_transport : Leaf f c → Implements (nounContract c) (jetT f)`, from
  `embed_value` and `embed_crash`;
- `nounContract_respects`: the specification is a function of the encoding,
  since `encNoun` is injective (`encNoun_inj`);
- `jet_close`, `jet_real`: `JSteps.close` and `real_of_jet` at the
  transported jet, so a verifier that accepts under the data jet for `f`
  accepts as an SKI term with `jetT f` in the jet's place.

**Why `toCell`.**  `embed_value` gives an encoding `ep` of the value with
`Enc p ep`, a relation: a cell's term may be a `Form` carrying its compiled
code (a battery pushed by `[1 …]`), and a `Form` does not reduce to a `Cell`.
A `Contract`'s `encO` is a function.  `toCellT` copies a noun's term
constructor by constructor, dropping code (`toCell_enc : Enc p ep → toCellT
⬝ ep ↠ encNoun p`), so the implementation's output is the function
`encNoun`.  This is the `toCell` wrapper `Nock2Ski/ProbeTree.lean` names as
not done; it is done here.

**Two outcomes against three.**  lean-ski's contract is total: `spec` has a
value for every `x : α`.  lean-nock's `cw w` is total too, two-valued (value
or crash): the third value of its contract, divergence, is the absence of a
derivation and has no encoding, so no term implements it and no row of the
circuit ends there (`embed_diverges`: the compiled term diverges exactly
where Nock has no outcome).  For the Λ words no subject diverges
(`word_crash_total`, by the guards Λ emits), which is what `Leaf f c` says:
`c` is the whole contract.  For a formula that does diverge somewhere, no
total `c` satisfies `Leaf f c`; `formContract f` restricts the domain to the
subjects on which Nock has an outcome (`Dom f`), takes that outcome as the
specification, and `jet_transport_dom` implements it with no hypothesis,
`embed_outcome` supplying the value.

**The two environments.**  `Word`, `phi` and `cw` live in `Nock.Comp`, which
cannot be imported here (`JetSpec.lean`).  The instances `dec_transport`
and `add_transport` take the hypotheses `Leaf decF decC` and `Leaf addF
addC`, which `Nock2Ski/JetWord.lean` proves from `leaf_correct` on the
lean-nock side: one constant each, both modules import `JetSpec.lean`,
nothing copied, as `Value.lean` joins the probe step.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- The code-dropping copy
-- ---------------------------------------------------------------------------

/-- The body of `toCell`: the noun (variable `1`) applied to its four
    continuations, `self` the variable `0`: `Atom b ↦ Atom b`, `Cell h t ↦
    Cell (self h) (self t)`, `Form h t k ↦ Cell (self h) (self t)`, `Err ↦
    Err`. -/
def toCellBody : OTerm :=
  .var 1 ⬝ₒ AtomC.toO
    ⬝ₒ absN [2, 3] (CellC.toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3))
    ⬝ₒ absN [2, 3, 4] (CellC.toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3))
    ⬝ₒ errO

/-- The generator, `λ self n. body`, and its fixpoint. -/
def toCellG : Term := toTerm (absN [0, 1] toCellBody)
def toCellFix : Term := yfix toCellG
/-- **`toCell`**: the closed term copying a noun's term code-free. -/
def toCellT : Term := Ycomb ⬝ toCellG

theorem toCellT_fix (x : Term) : WSteps (toCellT ⬝ x) (toCellFix ⬝ x) :=
  WSteps.left _ (Ycomb_unroll _)

/-- The unfolding: `toCell n ↠ n Atom (λh t. …) (λh t k. …) Err` with `self`
    the fixpoint. -/
theorem toCellFix_beta (x : Term) :
    WSteps (toCellFix ⬝ x)
      (x ⬝ AtomC
        ⬝ (absN [2, 3] (CellC.toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3))).close
            (overrideC (fun _ => K) [0, 1] [toCellFix, x])
        ⬝ (absN [2, 3, 4] (CellC.toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3))).close
            (overrideC (fun _ => K) [0, 1] [toCellFix, x])
        ⬝ errT) := by
  refine (WSteps.left _ (yfix_unroll _)).trans ?_
  have h := absN_beta_close [0, 1] toCellBody (fun _ => K) [toCellFix, x] rfl
  simp only [toCellBody, OTerm.close, close_toO, close_errO, overrideC_two_1] at h
  exact h

/-- The cell continuation on two fields. -/
theorem toCell_cellK (σ : Nat → Term) (eh et : Term) :
    WSteps ((absN [2, 3] (CellC.toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3))).close σ ⬝ eh ⬝ et)
      (CellC ⬝ (σ 0 ⬝ eh) ⬝ (σ 0 ⬝ et)) := by
  have h := absN_beta_close [2, 3] (CellC.toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3)) σ [eh, et] rfl
  simp only [OTerm.close, close_toO, overrideC, updC] at h
  exact h

/-- The form continuation on three fields: the code is dropped. -/
theorem toCell_formK (σ : Nat → Term) (eh et k : Term) :
    WSteps ((absN [2, 3, 4] (CellC.toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3))).close σ
        ⬝ eh ⬝ et ⬝ k)
      (CellC ⬝ (σ 0 ⬝ eh) ⬝ (σ 0 ⬝ et)) := by
  have h := absN_beta_close [2, 3, 4] (CellC.toO ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (.var 0 ⬝ₒ .var 3)) σ
    [eh, et, k] rfl
  simp only [OTerm.close, close_toO, overrideC, updC] at h
  exact h

/-- **`toCell` copies an encoding code-free**: on any encoding of `p`, the
    fixpoint reduces to `encNoun p`. -/
theorem toCellFix_enc : ∀ {p : Noun} {ep : Term}, Enc p ep → WSteps (toCellFix ⬝ ep) (encNoun p)
  | _, _, .atom n =>
    (toCellFix_beta _).trans ((atomT_elim _ _ _ _ _).trans (AtomC_red _))
  | _, _, .cell hh ht =>
    (toCellFix_beta _).trans ((cellT_elim _ _ _ _ _ _).trans
      ((toCell_cellK _ _ _).trans
        ((WSteps.left _ (WSteps.right _ (toCellFix_enc hh))).trans
          ((WSteps.right _ (toCellFix_enc ht)).trans (CellC_red _ _)))))
  | _, _, .form hh ht =>
    (toCellFix_beta _).trans ((formT_elim _ _ _ _ _ _ _).trans
      ((toCell_formK _ _ _ _).trans
        ((WSteps.left _ (WSteps.right _ (toCellFix_enc hh))).trans
          ((WSteps.right _ (toCellFix_enc ht)).trans (CellC_red _ _)))))

theorem toCell_enc {p : Noun} {ep : Term} (h : Enc p ep) : WSteps (toCellT ⬝ ep) (encNoun p) :=
  (toCellT_fix _).trans (toCellFix_enc h)

/-- `toCell` passes the crash through. -/
theorem toCell_err : WSteps (toCellT ⬝ errT) errT :=
  (toCellT_fix _).trans ((toCellFix_beta _).trans (errT_elim _ _ _ _))

-- ---------------------------------------------------------------------------
-- The encoding is injective
-- ---------------------------------------------------------------------------

theorem bl_inj : ∀ {bs cs : List Bool}, BitArith.bl bs = BitArith.bl cs → bs = cs
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | b :: bs, c :: cs, h => by
    have h' : Compose.pairT (Compose.boolT b) (BitArith.bl bs) =
        Compose.pairT (Compose.boolT c) (BitArith.bl cs) := by
      simp only [BitArith.bl, BitArith.consT, Term.app.injEq, true_and] at h
      exact h
    obtain ⟨h1, h2⟩ := pairT_inj h'
    rw [boolT_inj h1, bl_inj h2]

/-- **`encNoun` is injective.** -/
theorem encNoun_inj : ∀ {a b : Noun}, encNoun a = encNoun b → a = b
  | .atom m, .atom n, h => by
    simp only [encNoun_atom, atomT, Term.app.injEq, true_and] at h
    rw [bits_inj (bl_inj h)]
  | .atom _, .cell _ _, h => by simp only [encNoun_atom, encNoun_cell, atomT, cellT] at h; cases h
  | .cell _ _, .atom _, h => by simp only [encNoun_atom, encNoun_cell, atomT, cellT] at h; cases h
  | .cell h1 t1, .cell h2 t2, h => by
    simp only [encNoun_cell, cellT, Term.app.injEq, true_and] at h
    obtain ⟨e1, e2⟩ := pairT_inj h
    rw [encNoun_inj e1, encNoun_inj e2]

-- ---------------------------------------------------------------------------
-- The contract and the transported implementation
-- ---------------------------------------------------------------------------

/-- The output encoding: a value as `encNoun`, the crash as `Err`. -/
def encOut : Outcome → Term
  | .val p => encNoun p
  | .exit => errT

/-- **The data-jet contract of a total model** `c`: `spec := c`, the subject
    encoded by `encNoun`, the outcome by `encOut`. -/
def nounContract (c : Noun → Outcome) : Contract Noun Outcome := ⟨encNoun, encOut, c⟩

/-- **The transported implementation**: `λx. toCell (nockToSki f x)`. -/
def jetT (f : Noun) : Term := S ⬝ (K ⬝ toCellT) ⬝ nockToSki f

theorem jetT_red (f : Noun) (x : Term) : WSteps (jetT f ⬝ x) (toCellT ⬝ (nockToSki f ⬝ x)) :=
  .step (.S _ _ _) (.single (.left _ (.K _ _)))

/-- The compiled formula, copied code-free, reaches the model's encoded
    outcome on the encoded subject: the body of `Implements`. -/
theorem jet_step {f : Noun} {S : Noun} {o : Outcome} (h : NockEval S f o) :
    WSteps (jetT f ⬝ encNoun S) (encOut o) := by
  refine (jetT_red f _).trans ?_
  cases o with
  | val p =>
    obtain ⟨ep, hp, he⟩ := embed_value h (enc_encNoun S)
    exact (WSteps.right _ he).trans (toCell_enc hp)
  | exit => exact (WSteps.right _ (embed_crash h (enc_encNoun S))).trans toCell_err

/-- **`jet_transport`** (PLAN.md §3.1): a formula with a total model
    implements the model's data-jet contract, with no new proof of the
    function. -/
theorem jet_transport {f : Noun} {c : Noun → Outcome} (hc : Leaf f c) :
    Implements (nounContract c) (jetT f) :=
  fun S => jet_step (hc S)

/-- **The contract respects its encoding**: the specification is a function
    of the encoded input, since `encNoun` is injective. -/
theorem nounContract_respects (c : Noun → Outcome) : (nounContract c).Respects :=
  respects_of_inj fun _ _ h => encNoun_inj h

-- ---------------------------------------------------------------------------
-- What the jet licenses: the corollaries of `JSteps.close` and `real_of_jet`
-- ---------------------------------------------------------------------------

/-- **Closing the jet to the compiled formula**: a reduction with the data
    jet for `f` at the head variable `j` closes to a plain weak reduction
    with `jetT f` in the jet's place. -/
theorem jet_close {f : Noun} {c : Noun → Outcome} (hc : Leaf f c) {j : Nat} (σ : Nat → Term)
    (hσ : σ j = jetT f) {t u : OTerm} (h : JSteps (nounContract c) j t u) :
    WSteps (t.close σ) (u.close σ) :=
  h.close σ (by rw [hσ]; exact jet_transport hc)

/-- **A verifier that accepts under the jet accepts as an SKI term**: the
    open verifier `V`, reaching `K` on the statement and the realizer with
    the data jet for `f`, realizes its atom with `jetT f` closed in. -/
theorem jet_real {f : Noun} {c : Noun → Outcome} (hc : Leaf f c) {j : Nat} (σ : Nat → Term)
    (hσ : σ j = jetT f) {V : OTerm} {x r : Term}
    (h : JSteps (nounContract c) j (V ⬝ₒ x.toO ⬝ₒ r.toO) .K) : Real (.atom (V.close σ) x) r :=
  real_of_jet σ (by rw [hσ]; exact jet_transport hc) h

-- ---------------------------------------------------------------------------
-- The instances: Table C's `dec` and `add`
-- ---------------------------------------------------------------------------

/-- The data-jet contract of the Λ word `dec`: `spec := cw .dec` (`decC`). -/
def decContract : Contract Noun Outcome := nounContract decC
/-- The data-jet contract of the Λ word `add`: `spec := cw .add` (`addC`). -/
def addContract : Contract Noun Outcome := nounContract addC

/-- **`dec` transports.**  The hypothesis is `Nock2Ski/JetWord.lean`'s
    `leaf_dec`, lean-nock's `leaf_correct .dec` in the shared vocabulary. -/
theorem dec_transport (h : Leaf decF decC) : Implements decContract (jetT decF) :=
  jet_transport h

/-- **`add` transports.**  The hypothesis is `JetWord.lean`'s `leaf_add`. -/
theorem add_transport (h : Leaf addF addC) : Implements addContract (jetT addF) :=
  jet_transport h

theorem decContract_respects : decContract.Respects := nounContract_respects decC
theorem addContract_respects : addContract.Respects := nounContract_respects addC

-- ---------------------------------------------------------------------------
-- A partial formula: the contract on the subjects where Nock has an outcome
-- ---------------------------------------------------------------------------

/-- The subjects on which `f` has an outcome. -/
def Dom (f : Noun) : Type := {S : Noun // ∃ o, NockEval S f o}

/-- The outcome, chosen. -/
noncomputable def outcomeOf (f : Noun) (x : Dom f) : Outcome := Classical.choose x.2

theorem outcomeOf_spec (f : Noun) (x : Dom f) : NockEval x.1 f (outcomeOf f x) :=
  Classical.choose_spec x.2

/-- **The contract of any formula on its domain**: `spec` is Nock's outcome
    where there is one.  Off the domain the formula diverges, and so does
    the compiled term (`embed_diverges`): there is nothing to encode. -/
noncomputable def formContract (f : Noun) : Contract (Dom f) Outcome :=
  ⟨fun x => encNoun x.1, encOut, outcomeOf f⟩

theorem jet_transport_dom (f : Noun) : Implements (formContract f) (jetT f) :=
  fun x => jet_step (outcomeOf_spec f x)

theorem formContract_respects (f : Noun) : (formContract f).Respects :=
  respects_of_inj fun _ _ h => Subtype.ext (encNoun_inj h)

end Nock2Ski
