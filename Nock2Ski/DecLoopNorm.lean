import Nock2Ski.DecTermNock
import Nock2Ski.DecNorm
import Nock2Ski.DecLoop

open Nock
open Term

/-!
# The Λ loop with the normalised `dec` jet, as a `decterm` statement

Route (B): the compiled loop `while (top ≠ 0) dec` (`Nock2Ski/DecLoop.lean`)
with every occurrence of the compiled word `nockToSki decF` replaced by
`normJ J = S normT (K J)` (`Nock2Ski/DecNorm.lean`), `J` the jet's atom.  On
lean-ski's circuit with the `dec` jet, whose DEC table reads through
`K`-thunks (`DecJet.decRowI`), the normaliser hands the jet its argument
and the jet fires at every call.

- **`abstN P t`**: `t` with every occurrence of `P` replaced by `normJ J`;
  **`closeN`**: closing `J` to any term `Q` gives `t` with every
  occurrence of `P` replaced by `normJ Q` (`replT`).
- **`nockLoopV f s p`**: the statement's one verifier, `λ β w. (λ X.
  C[S X (K J)]) normT`, `C` the check `checkT f s p` with every occurrence
  of the compiled word replaced (one copy of `normT` in the statement's
  heap); it is `vsOK`, and closed it reduces to the replaced check
  (`checkN_close`).
- **`nockloop_close`**: an accepted proof of the statement shows that M4c's
  check of `*[s f] = p`, with every occurrence of the compiled word replaced
  by `normJ (nockToSki decF)`, reaches `K` (lean-ski's
  `dectermExport_close`, the bare word implementing the contract,
  `dec_impl_bare`, and so `normJ` of it, `normJ_impl`).

What is not proved here: that this replaced check reaching `K` gives
`*[s f] = p` (the compiler's correctness with the replacement, and its
converse `nock_of_eqn_K`); `normDec_enc` is the per-call fact it would rest
on (lean-ski's `todo/dec-norm.md`).
-/

namespace Nock2Ski

open ComposedDText DecTerm DecNorm

/-- `t` with every occurrence of `P` replaced by `Q`. -/
def replT (P Q : _root_.Term) : _root_.Term → _root_.Term
  | .S => if _root_.Term.S = P then Q else .S
  | .K => if _root_.Term.K = P then Q else .K
  | .I => if _root_.Term.I = P then Q else .I
  | .app f x => if _root_.Term.app f x = P then Q else .app (replT P Q f) (replT P Q x)

/-- The normalised jet, open in the jet's atom. -/
def normJO : OTerm := .S ⬝ₒ normT.toO ⬝ₒ (.K ⬝ₒ .var JD)

/-- Every occurrence of `P` in `t` replaced by `normJ J`. -/
def abstN (P : _root_.Term) : _root_.Term → OTerm
  | .S => if _root_.Term.S = P then normJO else .S
  | .K => if _root_.Term.K = P then normJO else .K
  | .I => if _root_.Term.I = P then normJO else .I
  | .app f x => if _root_.Term.app f x = P then normJO else .app (abstN P f) (abstN P x)

theorem normJO_close (σ : Nat → _root_.Term) : normJO.close σ = normJ (σ JD) := by
  show _ ⬝ normT.toO.close σ ⬝ (K ⬝ σ JD) = _
  rw [close_toO]; rfl

theorem closeN (P : _root_.Term) (σ : Nat → _root_.Term) : ∀ t : _root_.Term, (abstN P t).close σ = replT P (normJ (σ JD)) t
  | .S => by
    show OTerm.close σ (if _root_.Term.S = P then normJO else .S) = (if _root_.Term.S = P then _ else .S)
    by_cases h : _root_.Term.S = P
    · rw [if_pos h, if_pos h, normJO_close]
    · rw [if_neg h, if_neg h]; rfl
  | .K => by
    show OTerm.close σ (if _root_.Term.K = P then normJO else .K) = (if _root_.Term.K = P then _ else .K)
    by_cases h : _root_.Term.K = P
    · rw [if_pos h, if_pos h, normJO_close]
    · rw [if_neg h, if_neg h]; rfl
  | .I => by
    show OTerm.close σ (if _root_.Term.I = P then normJO else .I) = (if _root_.Term.I = P then _ else .I)
    by_cases h : _root_.Term.I = P
    · rw [if_pos h, if_pos h, normJO_close]
    · rw [if_neg h, if_neg h]; rfl
  | .app f x => by
    show OTerm.close σ (if _root_.Term.app f x = P then normJO else .app (abstN P f) (abstN P x)) =
      (if _root_.Term.app f x = P then _ else .app (replT P _ f) (replT P _ x))
    by_cases h : _root_.Term.app f x = P
    · rw [if_pos h, if_pos h, normJO_close]
    · rw [if_neg h, if_neg h]
      show OTerm.close σ (abstN P f) ⬝ OTerm.close σ (abstN P x) = _
      rw [closeN P σ f, closeN P σ x]

theorem normJO_occ {x : Nat} (h : Occ x normJO) : x = JD := by
  have : ∀ x, ¬ Occ x normT.toO := fun x => OTerm.not_occ (mem_toO _ _)
  rcases Circuit.occ_app h with h | h
  · rcases Circuit.occ_app h with h | h
    · cases h
    · exact absurd h (this x)
  · rcases Circuit.occ_app h with h | h
    · cases h
    · cases h; rfl

theorem abstN_occ (P : _root_.Term) : ∀ (t : _root_.Term) {x : Nat}, Occ x (abstN P t) → x = JD
  | .S, x, hx | .K, x, hx | .I, x, hx => by
    simp only [abstN] at hx
    split at hx
    · exact normJO_occ hx
    · cases hx
  | .app f a, x, hx => by
    simp only [abstN] at hx
    split at hx
    · exact normJO_occ hx
    · cases hx with
      | left _ hf => exact abstN_occ P f hf
      | right _ ha => exact abstN_occ P a ha

/-- The variable that carries the one shared copy of `normT`. -/
def XN : Nat := 5

/-- The normalised jet over the shared `normT`: `S X (K J)`. -/
def normJX : OTerm := .S ⬝ₒ .var XN ⬝ₒ (.K ⬝ₒ .var JD)

/-- Every occurrence of `P` in `t` replaced by `S X (K J)`. -/
def abstX (P : _root_.Term) : _root_.Term → OTerm
  | .S => if _root_.Term.S = P then normJX else .S
  | .K => if _root_.Term.K = P then normJX else .K
  | .I => if _root_.Term.I = P then normJX else .I
  | .app f x => if _root_.Term.app f x = P then normJX else .app (abstX P f) (abstX P x)

theorem closeX (P : _root_.Term) (σ : Nat → _root_.Term) : ∀ t : _root_.Term,
    (abstX P t).close σ = replT P (S ⬝ σ XN ⬝ (K ⬝ σ JD)) t
  | .S => by
    show OTerm.close σ (if _root_.Term.S = P then normJX else .S) = (if _root_.Term.S = P then _ else .S)
    by_cases h : _root_.Term.S = P
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl
  | .K => by
    show OTerm.close σ (if _root_.Term.K = P then normJX else .K) = (if _root_.Term.K = P then _ else .K)
    by_cases h : _root_.Term.K = P
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl
  | .I => by
    show OTerm.close σ (if _root_.Term.I = P then normJX else .I) = (if _root_.Term.I = P then _ else .I)
    by_cases h : _root_.Term.I = P
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]; rfl
  | .app f x => by
    show OTerm.close σ (if _root_.Term.app f x = P then normJX else .app (abstX P f) (abstX P x)) =
      (if _root_.Term.app f x = P then _ else .app (replT P _ f) (replT P _ x))
    by_cases h : _root_.Term.app f x = P
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]
      show OTerm.close σ (abstX P f) ⬝ OTerm.close σ (abstX P x) = _
      rw [closeX P σ f, closeX P σ x]

theorem abstX_occ (P : _root_.Term) : ∀ (t : _root_.Term) {x : Nat}, Occ x (abstX P t) → x = JD ∨ x = XN
  | .S, x, hx | .K, x, hx | .I, x, hx => by
    simp only [abstX] at hx
    split at hx
    · exact normJX_occ hx
    · cases hx
  | .app f a, x, hx => by
    simp only [abstX] at hx
    split at hx
    · exact normJX_occ hx
    · cases hx with
      | left _ hf => exact abstX_occ P f hf
      | right _ ha => exact abstX_occ P a ha
where
  normJX_occ {x : Nat} (h : Occ x normJX) : x = JD ∨ x = XN := by
    rcases Circuit.occ_app h with h | h
    · rcases Circuit.occ_app h with h | h
      · cases h
      · cases h; exact .inr rfl
    · rcases Circuit.occ_app h with h | h
      · cases h
      · cases h; exact .inl rfl

/-- The check with every occurrence of the compiled word normalised, one
    copy of `normT` shared through `X` (so the statement's heap holds it
    once): `(λ X. C[S X (K J)]) normT`. -/
def checkN (f s p : Noun) : OTerm := absN [XN] (abstX (nockToSki decF) (checkT f s p)) ⬝ₒ normT.toO

/-- The statement's one verifier. -/
def nockLoopV (f s p : Noun) : OTerm := verT (checkN f s p)

theorem checkN_occ (f s p : Noun) {x : Nat} (h : Occ x (checkN f s p)) : x = JD := by
  rcases Circuit.occ_app h with h | h
  · obtain ⟨h1, h2⟩ := Circuit.occ_absN [XN] h
    rcases abstX_occ _ _ h1 with e | e
    · exact e
    · exact absurd (List.mem_singleton.2 e) h2
  · exact absurd h (OTerm.not_occ (mem_toO _ _))

/-- Closing the shared check: it reduces to the replaced check. -/
theorem checkN_close (f s p : Noun) (σ : Nat → _root_.Term) :
    WSteps ((checkN f s p).close σ) (replT (nockToSki decF) (normJ (σ JD)) (checkT f s p)) := by
  have hb := absN_beta_close [XN] (abstX (nockToSki decF) (checkT f s p)) σ [normT] rfl
  have e : (checkN f s p).close σ = _root_.appT ((absN [XN] (abstX (nockToSki decF) (checkT f s p))).close σ) [normT] := by
    show _ ⬝ normT.toO.close σ = _
    rw [close_toO]; rfl
  rw [e]
  refine hb.trans ?_
  rw [closeX]
  have h1 : overrideC σ [XN] [normT] XN = normT := by
    show updC σ XN normT XN = normT
    simp [updC]
  have h2 : overrideC σ [XN] [normT] JD = σ JD := Mach.overrideC_notin _ _ _ _ (by decide)
  rw [h1, h2]
  exact .refl _

theorem nockLoopV_vsOK (f s p : Noun) : vsOK [nockLoopV f s p] = true := by
  have h : occOK (nockLoopV f s p) = true := occOK_of fun x hx => by
    obtain ⟨h1, _⟩ := Circuit.occ_absN [0, 1] hx
    exact checkN_occ _ _ _ h1
  simp only [vsOK, List.length_cons, List.length_nil, Nat.lt_add_one, decide_true, List.all_cons, h,
    List.all_nil, Bool.and_self]

/-- **An accepted proof of the normalised loop's statement**: M4c's check of
    `*[s f] = p`, every occurrence of the compiled word replaced by `normJ
    (nockToSki decF)`, reaches `K`. -/
theorem nockloop_close {f s p : Noun} {W : Nat} {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs (Circuit.compDAirsG [nockLoopV f s p] W) = true) (hacc : Circuit.AcceptedP Rs ts) :
    WSteps (replT (nockToSki decF) (normJ (nockToSki decF)) (checkT f s p)) _root_.Term.K := by
  have hk := Circuit.dectermExport_close (nockLoopV_vsOK f s p) (List.mem_singleton.2 rfl)
    (fun x hx => checkN_occ _ _ _ hx) hs hacc dec_impl_bare
  have hc := checkN_close f s p (DecPre.envD (nockToSki decF))
  have e : DecPre.envD (nockToSki decF) JD = nockToSki decF := by
    show (if JD = JD then _ else _) = _; rw [if_pos rfl]
  rw [e] at hc
  exact (Compose.wsteps_K_iff hc).1 hk

end Nock2Ski
