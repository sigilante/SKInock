import Nock2Ski.JetTransport
import Ski.DecPreSound

open Nock
open Term DataJet

/-!
# The bridge to lean-ski's `dec` data jet

lean-ski states the `dec` jet's contract over its own copy of the noun
encoding (`DecJet.Nn`, `DecJet.encNn`, `DecJet.decSpec`,
`DecJet.decContract` on the domain `DecJet.Dom`: well-formed nouns whose
head atom has at most 32 bits), and `Circuit.decpreExport_sound` takes an
implementation of that contract as its hypothesis `hP`.  skinock's
transported jet implements `nounContract decC` over `Noun`
(`dec_transport`).  This module joins the two:

- `toNoun : DecJet.Nn → Noun`, an atom's bits read as their value;
- `encNn_eq : s.wf → DecJet.encNn s = encNoun (toNoun s)`: the two
  encodings agree on canonical bits (skinock's `bits` is lean-ski's
  `bitsN`, `bitsN_val`);
- `encO_eq : DecJet.encO (DecJet.decSpec s) = encOut (decC (toNoun s))`
  on well-formed `s` (`decB_bitsN`);
- **`dec_impl_lean : Implements DecJet.decContract (jetT decF)`**, from
  `dec_transport`, which discharges `decpreExport_sound`'s `hP`:
  `decpre_proof_nock`.
-/

namespace Nock2Ski

/-- A lean-ski noun over bit lists as a Nock noun. -/
def toNoun : DecJet.Nn → Noun
  | .atom bs => .atom (BitArith.val bs)
  | .cell h t => .cell (toNoun h) (toNoun t)

/-- skinock's `bits` is lean-ski's `bitsN`. -/
theorem bits_eq_bitsN : ∀ n, bits n = ComposedDText.bitsN n
  | 0 => by rw [ComposedDText.bitsN_zero, bits]
  | n + 1 => by
    rw [bits, ComposedDText.bitsN_pos (Nat.succ_pos n), bits_eq_bitsN ((n + 1) / 2)]

/-- Canonical bits are their value's bits. -/
theorem bits_val {bs : List Bool} (h : DecJet.canonB bs = true) : bits (BitArith.val bs) = bs := by
  rw [bits_eq_bitsN]; exact ComposedDText.bitsN_val h

/-- **The encodings agree** on well-formed nouns. -/
theorem encNn_eq : ∀ {s : DecJet.Nn}, s.wf = true → DecJet.encNn s = encNoun (toNoun s)
  | .atom bs, h => by
    show DecJet.atomT (BitArith.bl bs) = atomT (bitsT (bits (BitArith.val bs)))
    rw [bits_val h]; rfl
  | .cell hd tl, h => by
    simp only [DecJet.Nn.wf, Bool.and_eq_true] at h
    show DecJet.cellT (DecJet.encNn hd) (DecJet.encNn tl) = cellT (encNoun (toNoun hd)) (encNoun (toNoun tl))
    rw [encNn_eq h.1, encNn_eq h.2]; rfl

/-- **The outcomes agree** on well-formed nouns: `decSpec` is `decC`. -/
theorem encO_eq {s : DecJet.Nn} (hs : s.wf = true) :
    DecJet.encO (DecJet.decSpec s) = encOut (decC (toNoun s)) := by
  match s, hs with
  | .atom _, _ => rfl
  | .cell (.cell _ _) _, _ => rfl
  | .cell (.atom []) _, _ => rfl
  | .cell (.atom (b :: bs)) r, hs =>
    simp only [DecJet.Nn.wf, Bool.and_eq_true] at hs
    have hc : DecJet.canonB (b :: bs) = true := hs.1
    have hv := (bits_val hc)
    have hpos : BitArith.val (b :: bs) ≠ 0 := by
      intro h0; rw [h0] at hv; simp [bits] at hv
    obtain ⟨m, hm⟩ : ∃ m, BitArith.val (b :: bs) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero hpos).symm⟩
    have hd : DecJet.decB (b :: bs) = bits m := by
      rw [← hv, hm, bits_eq_bitsN, bits_eq_bitsN, ComposedDText.decB_bitsN]
    show DecJet.encNn (.cell (.atom (DecJet.decB (b :: bs))) r) =
      encOut (decC (.cell (.atom (BitArith.val (b :: bs))) (toNoun r)))
    rw [hm, hd]
    show DecJet.cellT (DecJet.atomT (BitArith.bl (bits m))) (DecJet.encNn r) =
      cellT (atomT (bitsT (bits m))) (encNoun (toNoun r))
    rw [encNn_eq hs.2]; rfl

/-- **The transported `dec` jet implements lean-ski's `dec` contract.** -/
theorem dec_impl_lean : Implements DecJet.decContract (jetT decF) := fun s => by
  show WSteps (jetT decF ⬝ DecJet.encNn s.1) (DecJet.encO (DecJet.decSpec s.1))
  rw [encNn_eq s.2.1, encO_eq s.2.1]
  exact dec_transport (toNoun s.1)

/-- `decC` on a well-formed noun is `decSpec`. -/
theorem decC_toNoun {s : DecJet.Nn} (hs : s.wf = true) :
    decC (toNoun s) = match DecJet.decSpec s with
      | some o => .val (toNoun o)
      | none => .exit := by
  match s, hs with
  | .atom _, _ => rfl
  | .cell (.cell _ _) _, _ => rfl
  | .cell (.atom []) _, _ => rfl
  | .cell (.atom (b :: bs)) r, hs =>
    simp only [DecJet.Nn.wf, Bool.and_eq_true] at hs
    have hv := DecJet.decB_val hs.1 (List.cons_ne_nil b bs)
    show decC (.cell (.atom (BitArith.val (b :: bs))) (toNoun r)) =
      .val (.cell (.atom (BitArith.val (DecJet.decB (b :: bs)))) (toNoun r))
    rw [← hv]; rfl

/-- **`decpreExport_sound` with its hypothesis discharged**: an accepted
    proof of `decpre p` holds in its memory a subject `s` in the jet's
    domain on which Nock's `phi .dec` yields a cell headed by the atom `p`. -/
theorem decpre_proof_nock {p W : Nat} {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs (Circuit.compDAirs p W) = true) (hacc : Circuit.AcceptedP Rs ts) :
    ∃ (s : DecJet.Dom) (r : Noun), NockEval (toNoun s.1) decF (.val (.cell (.atom p) r)) := by
  obtain ⟨_, _, _, _, _, _, _, s, _, _, _, _, d, r, hd, hv⟩ := Circuit.decpreExport_sound dec_impl_lean hs hacc
  refine ⟨s, toNoun r, ?_⟩
  have h := leaf_dec (toNoun s.1)
  rw [decC_toNoun s.2.1, hd] at h
  rw [← hv]; exact h

end Nock2Ski

namespace Nock2Ski

/-- The head of `phi .dec`, `[7 [0 2] <guarded-dec>]`, after its opcode. -/
def decHeadT : Noun :=
  n! "[[0 2] 6 [3 0 1] [0 0] 6 [5 [1 0] 0 1] [0 0] 8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]"

theorem decF_cells : decF = .cell (.cell (.atom 7) decHeadT) (.cell (.atom 0) (.atom 3)) := rfl

theorem axisPath_3 : axisPath 3 = [true] := by
  rw [axisPath_rec (by omega), axisPath_one]; rfl

/-- **The bare compiled word implements the transported contract**:
    `nockToSki decF` on an encoded stack reduces to the encoded outcome
    itself, with no `toCell` copy.  The head is an atom, whose encoding is
    unique (`Enc.atom_inv`); the tail is the subject's own tail (`[0 3]`);
    `force` and `Cell` rebuild the code-free cell. -/
theorem decF_bare (S : Noun) : WSteps (nockToSki decF ⬝ encNoun S) (encOut (decC S)) := by
  have hl := leaf_dec S
  cases hdc : decC S with
  | exit => rw [hdc] at hl; exact embed_crash_encNoun hl
  | val p =>
    rw [hdc] at hl
    match S, hdc with
    | .cell (.atom (n + 1)) r, hdc =>
      have hp : p = .cell (.atom n) r := by
        simp only [decC] at hdc; exact (Nock.Outcome.val.inj hdc).symm
      subst hp
      rw [decF_cells] at hl ⊢
      cases hl with
      | autocons h1 _ =>
        obtain ⟨eh, hh, hred⟩ := embed_value_encNoun h1
        rw [Enc.atom_inv hh] at hred
        have e1 := step_autocons (.atom 7) decHeadT (.cell (.atom 0) (.atom 3)) (encNoun (.cell (.atom (n + 1)) r))
        have e2 : WSteps (nockToSki (.cell (.atom 0) (.atom 3)) ⬝ encNoun (.cell (.atom (n + 1)) r)) (encNoun r) := by
          have := step_op0 2 (encNoun (.cell (.atom (n + 1)) r))
          rw [show (2 + 1 : Nat) = 3 from rfl, axisPath_3] at this
          exact this.trans (tl_cellT _ _)
        refine e1.trans ((((WSteps.right forceT hred).left _)).trans ((force_spec _ _).trans
          ((consK_beta _ _).trans ((((WSteps.right forceT e2).left _)).trans ((force_spec _ _).trans ?_)))))
        exact CellC_red _ _

/-- **`dec_impl_bare`**: the bare compiled word implements lean-ski's `dec`
    contract, so a term whose every `nockToSki decF` is the jet's atom
    closes, with the word in the jet's place, to the term itself. -/
theorem dec_impl_bare : Implements DecJet.decContract (nockToSki decF) := fun s => by
  show WSteps (nockToSki decF ⬝ DecJet.encNn s.1) (DecJet.encO (DecJet.decSpec s.1))
  rw [encNn_eq s.2.1, encO_eq s.2.1]
  exact decF_bare (toNoun s.1)

end Nock2Ski
