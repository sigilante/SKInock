import Nock2Ski.DecBridge
import Ski.DecTerm

open Nock
open Term

/-!
# A Nock claim on lean-ski's circuit with the `dec` jet

lean-ski's `decterm` statements (`Ski/DecTerm.lean`, branch `dec-loop`) take
any public verifiers open in the jet's atom `JD`.  This module builds one
from a Nock claim `*[s f] = p` and proves what an accepted proof of it means.

- **`abstJ P t`**: the term `t` with every occurrence of the subterm `P`
  replaced by the variable `JD` (the jet's licensed roots).
  `abstJ_close`: closing `JD` to `P` gives `t` back; `abstJ_occ`: `JD` is
  its only variable.
- **`checkT f s p = eqn (nockToSki f ⬝ encNoun s) (encNoun p)`**, M4c's
  check (`nock_of_eqn_K`), and its jetted form **`checkJ f s p = abstJ
  (nockToSki decF) (checkT f s p)`**: every occurrence of the compiled word
  `dec` is the jet.  The statement's verifier is `verT (checkJ f s p) = λ β
  w. checkJ f s p`.
- **`nockdec_sound`**: an accepted proof of that statement (the AIRs
  `compDAirsG [verT (checkJ f s p)] W`) shows `*[s f] = p`: lean-ski's
  `dectermExport_close` with the bare word as the implementation
  (`dec_impl_bare`) closes the jetted check to `checkT f s p` itself
  (`abstJ_close`), and `nock_of_eqn_K` reads it as a Nock derivation.

The statement exists for every formula, but the jet fires only on subjects
laid out in memory (`DecJet.readNn`): here the literal `encNoun s` the
check hands the word when `f` is the word itself (`decF`) or begins with
it.  Inside a loop the word's argument is a computed value, never laid out,
and the prover's run stops at the jet (`bench/NockDecLoop.lean probe`).
-/

namespace Nock2Ski

open ComposedDText DecTerm

/-- Replace every occurrence of `P` in `t` by the jet's variable. -/
def abstJ (P : Term) : Term → OTerm
  | .S => if Term.S = P then .var JD else .S
  | .K => if Term.K = P then .var JD else .K
  | .I => if Term.I = P then .var JD else .I
  | .app f x => if Term.app f x = P then .var JD else .app (abstJ P f) (abstJ P x)

theorem abstJ_close (P : Term) (σ : Nat → Term) (hσ : σ JD = P) : ∀ t : Term, (abstJ P t).close σ = t
  | .S => by
    show OTerm.close σ (if Term.S = P then .var JD else .S) = _
    by_cases h : Term.S = P
    · rw [if_pos h]; show σ JD = _; rw [hσ, h]
    · rw [if_neg h]; rfl
  | .K => by
    show OTerm.close σ (if Term.K = P then .var JD else .K) = _
    by_cases h : Term.K = P
    · rw [if_pos h]; show σ JD = _; rw [hσ, h]
    · rw [if_neg h]; rfl
  | .I => by
    show OTerm.close σ (if Term.I = P then .var JD else .I) = _
    by_cases h : Term.I = P
    · rw [if_pos h]; show σ JD = _; rw [hσ, h]
    · rw [if_neg h]; rfl
  | .app f x => by
    show OTerm.close σ (if Term.app f x = P then .var JD else .app (abstJ P f) (abstJ P x)) = _
    by_cases h : Term.app f x = P
    · rw [if_pos h]; show σ JD = _; rw [hσ, h]
    · rw [if_neg h]
      show OTerm.close σ (abstJ P f) ⬝ OTerm.close σ (abstJ P x) = f ⬝ x
      rw [abstJ_close P σ hσ f, abstJ_close P σ hσ x]

theorem abstJ_occ (P : Term) : ∀ (t : Term) {x : Nat}, Occ x (abstJ P t) → x = JD
  | .S, x, hx | .K, x, hx | .I, x, hx => by
    simp only [abstJ] at hx
    split at hx
    · cases hx; rfl
    · cases hx
  | .app f a, x, hx => by
    simp only [abstJ] at hx
    split at hx
    · cases hx; rfl
    · cases hx with
      | left _ hf => exact abstJ_occ P f hf
      | right _ ha => exact abstJ_occ P a ha

/-- M4c's check of a Nock claim `*[s f] = p`. -/
def checkT (f s p : Noun) : Term := eqnFix ⬝ (nockToSki f ⬝ encNoun s) ⬝ encNoun p

/-- The check with the compiled word `dec` as the jet. -/
def checkJ (f s p : Noun) : OTerm := abstJ (nockToSki decF) (checkT f s p)

/-- The statement's one verifier. -/
def nockDecV (f s p : Noun) : OTerm := verT (checkJ f s p)

theorem occOK_of {V : OTerm} (h : ∀ x, Occ x V → x = JD) : occOK V = true := by
  unfold occOK
  refine List.all_eq_true.2 fun x hx => ?_
  have := h x (occ_of_mem ((OTerm.mem_vars x V).2 hx))
  rw [this]; exact beq_self_eq_true _
where
  occ_of_mem {x : Nat} : ∀ {t : OTerm}, t.mem x = true → Occ x t
    | .var y, h => by
      have : y = x := beq_iff_eq.1 h
      subst this; exact .var _
    | .app f a, h => by
      rcases Bool.or_eq_true_iff.1 h with h | h
      · exact .left _ (occ_of_mem h)
      · exact .right _ (occ_of_mem h)
    | .S, h | .K, h | .I, h => by cases h

theorem nockDecV_vsOK (f s p : Noun) : vsOK [nockDecV f s p] = true := by
  have h : occOK (nockDecV f s p) = true := occOK_of fun x hx => by
    obtain ⟨h1, _⟩ := Circuit.occ_absN [0, 1] hx
    exact abstJ_occ _ _ h1
  simp only [vsOK, List.length_cons, List.length_nil, Nat.lt_add_one, decide_true, List.all_cons, h,
    List.all_nil, Bool.and_self]

/-- **An accepted proof of the jetted Nock claim is a Nock derivation**:
    `*[s f] = p`. -/
theorem nockdec_sound {f s p : Noun} {W : Nat} {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs (Circuit.compDAirsG [nockDecV f s p] W) = true) (hacc : Circuit.AcceptedP Rs ts) :
    NockEval s f (.val p) := by
  have hk := Circuit.dectermExport_close (nockDecV_vsOK f s p) (List.mem_singleton.2 rfl)
    (fun x hx => abstJ_occ _ _ hx) hs hacc dec_impl_bare
  have e : (checkJ f s p).close (DecPre.envD (nockToSki decF)) = checkT f s p :=
    abstJ_close _ _ (by show (if JD = JD then _ else _) = _; rw [if_pos rfl]) _
  rw [e] at hk
  exact nock_of_eqn_K hk

end Nock2Ski
