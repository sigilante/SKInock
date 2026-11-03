import Nock.Comp
import Nock.Mock
import Nock2Ski.JetSpec

open Nock
open Noun

/-!
# The Λ words' leaf contracts, in the shared vocabulary (M5, the Nock side)

This module imports lean-nock only (`Nock.Comp`, `Nock.Mock`).  It reads
lean-nock's leaf proofs off as `Leaf` statements about the formulas and
models `JetSpec.lean` writes out, which `Nock2Ski/JetTransport.lean`
imports and composes with `jet_transport`:

- `leaf_word w : Leaf (phi w) (cw w)` is `leaf_correct w` itself;
- `decF_eq`, `addF_eq`: the formulas of `JetSpec.lean` are `phi .dec` and
  `phi .add` (`rfl`); `decC_eq`, `addC_eq`: the models are `cw .dec` and
  `cw .add` (by cases on the subject);
- `leaf_dec : Leaf decF decC` and `leaf_add : Leaf addF addC`, which
  `JetTransport.lean`'s `dec_transport` and `add_transport` compose in.

lean-nock's three-valued contract (`Nock/Mock.lean`): `word_jet_sound w :
ThreeValued (phi w) (wordJet w)`, the C model as a jet that returns or
exits and never punts.  `dec_three_valued`, `add_three_valued` are its
instances, kept here beside the two-valued `Leaf` so that the README can
name both: the third value, divergence, is excluded for every word
(`word_crash_total`), which is what makes `cw w` total and `Leaf` the
whole contract.
-/

namespace Nock2Ski

/-- lean-nock's leaf correctness, in the shared shape. -/
theorem leaf_word (w : Word) : Leaf (phi w) (cw w) := leaf_correct w

theorem decF_eq : decF = phi .dec := rfl
theorem addF_eq : addF = phi .add := rfl

theorem decC_eq : ∀ S, decC S = cw .dec S
  | atom _ => rfl
  | cell (atom 0) _ => rfl
  | cell (atom (_ + 1)) _ => rfl
  | cell (cell _ _) _ => rfl

theorem addC_eq : ∀ S, addC S = cw .add S
  | atom _ => rfl
  | cell (atom _) (atom _) => rfl
  | cell (cell _ _) (atom _) => rfl
  | cell (cell _ _) (cell _ _) => rfl
  | cell (atom _) (cell (cell _ _) _) => rfl
  | cell (atom _) (cell (atom _) _) => rfl

/-- **Table C's `dec`, in the shape `dec_transport` composes in.** -/
theorem leaf_dec : Leaf decF decC := fun S => by
  rw [decF_eq, decC_eq]
  exact leaf_correct .dec S

/-- **Table C's `add`, in the shape `add_transport` composes in.** -/
theorem leaf_add : Leaf addF addC := fun S => by
  rw [addF_eq, addC_eq]
  exact leaf_correct .add S

/-- The words have an outcome on every subject: no divergence for a jet to
    mishandle (lean-nock's `word_crash_total`). -/
theorem leaf_total {f : Noun} {c : Noun → Outcome} (h : Leaf f c) (S : Noun) :
    ∃ o, NockEval S f o := ⟨c S, h S⟩

/-- lean-nock's three-valued contract for `dec` and `add`, by the C model as
    a jet that returns or exits. -/
theorem dec_three_valued : ThreeValued decF (wordJet .dec) := word_jet_sound .dec
theorem add_three_valued : ThreeValued addF (wordJet .add) := word_jet_sound .add

end Nock2Ski
