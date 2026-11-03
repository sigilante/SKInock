import Nock2Ski.InterpEnc

open Term

/-!
# Head length: the measure for the converse simulation

Milestone M4e of `PLAN.md`.  The simulation (`Nock2Ski/Embed.lean`) carries
a `NockEval` derivation to weak reduction of the compiled term.  Its
converse, "if the compiled term reaches a weak head normal form then Nock
has an outcome", is proved by contraposition through a measure on the SKI
side: `HLen t n`, the term `t` reaches a weak head normal form in exactly
`n` normal-order contractions.  Three facts carry it, all consequences
of determinism and of lean-ski's `par_step_le`:

- a head reduction of `j` steps leaves exactly `n - j` (`hlen_steps`);
- a weak reduction, anywhere in the term, leaves at most `n`
  (`hlen_wsteps`: weak reduction never lengthens the run to a normal
  form);
- if `t ⬝ a` normalizes, `t` does, in no more steps (`hlen_app`).

These are lean-ski's `StepsN.tail`, `StepsN.wtail`, `StepsN.app_left`
(`Ski/Converse.lean`), copied here because that module reaches
`Ski.Words`, whose root-level `Outcome` cannot be imported beside
lean-nock's.

## Strictness from the primitives' head reductions

Every Nock step that the compiled code takes is a `force` (or `cel`,
`inc`, `ifn`) on the operand's term, and `force X k` head-reduces to `X`
applied to its four continuations in at least one contraction, so the
operand's head length is strictly below the node's.  Those head
reductions are computed symbolically: `hred` is lean-ski's `ostep?`
iterated at the head of an open term with a count, sound by `OStep.close`
(`hred_stepsN`), and `pendCheck`/`contCheck` are the decidable shape
checks `decide +kernel` runs on `forceT.toO ⬝ₒ .var 0 ⬝ₒ .var 1` and its
siblings: the result is headed by the operand's variable with four
arguments (`pendCheck`), or by the continuation's variable with one
argument that weakly normalizes to the operand's encoding (`contCheck`).
`pendCheck_sound` and `contCheck_sound` turn a passed check into the
strict bound on any closing.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- Counted head reduction (lean-ski's `Ski/Converse.lean`, copied)
-- ---------------------------------------------------------------------------

/-- Exactly `n` contractions. -/
inductive StepsN : Nat → Term → Term → Prop
  | refl (t : Term) : StepsN 0 t t
  | step {n : Nat} {t t' u : Term} (h : Step t t') (hs : StepsN n t' u) : StepsN (n + 1) t u

theorem StepsN.steps {n : Nat} {t u : Term} (h : StepsN n t u) : Steps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step h ih

theorem steps_counted {t u : Term} (h : Steps t u) : ∃ n, StepsN n t u := by
  induction h with
  | refl t => exact ⟨0, .refl t⟩
  | step h _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step h hn⟩

theorem StepsN.after_step {t t' w : Term} {n : Nat} (s : Step t t') (hw : StepsN n t w)
    (ww : Whnf w) : ∃ m, n = m + 1 ∧ StepsN m t' w := by
  cases hw with
  | refl _ => exact (ww.no_step s).elim
  | step s' hw' =>
    have e := Step.det s' s
    subst e
    exact ⟨_, rfl, hw'⟩

/-- **Weak reduction does not lengthen the run to a normal form**: a head
    step of `t` costs a parallel reduct of `t` at most one head step
    (`par_step_le`), and a parallel reduct of a weak head normal form is
    one. -/
theorem StepsN.par {t u w : Term} {n : Nat} (hp : Par t u) (hw : StepsN n t w) (ww : Whnf w) :
    ∃ m w', m ≤ n ∧ StepsN m u w' ∧ Whnf w' := by
  induction hw generalizing u with
  | refl t => exact ⟨0, u, Nat.le_refl 0, .refl u, hp.whnf ww⟩
  | step s _ ih =>
    obtain ⟨u1, h1, h2⟩ := par_step_le s hp
    obtain ⟨m, w', hm, hs, hw'⟩ := ih h2 ww
    cases h1 with
    | inl e => exact ⟨m, w', Nat.le_succ_of_le hm, e ▸ hs, hw'⟩
    | inr s' => exact ⟨m + 1, w', Nat.succ_le_succ hm, .step s' hs, hw'⟩

theorem StepsN.wtail {t u w : Term} {n : Nat} (h : WSteps t u) (hw : StepsN n t w) (ww : Whnf w) :
    ∃ m w', m ≤ n ∧ StepsN m u w' ∧ Whnf w' := by
  induction h generalizing n w with
  | refl _ => exact ⟨n, w, Nat.le_refl n, hw, ww⟩
  | step s _ ih =>
    obtain ⟨m, w1, hm, hs1, hw1⟩ := StepsN.par s.par hw ww
    obtain ⟨m', w2, hm', hs2, hw2⟩ := ih hs1 hw1
    exact ⟨m', w2, Nat.le_trans hm' hm, hs2, hw2⟩

theorem whnf_fn {t a : Term} (h : Whnf (t ⬝ a)) : Whnf t := by
  cases h with
  | S1 _ => exact .S
  | S2 x _ => exact .S1 x
  | K1 _ => exact .K

/-- If `t ⬝ a` normalizes, so does `t`: normal order reduces the head first. -/
theorem StepsN.app_left : ∀ {n : Nat} {t a w : Term}, StepsN n (t ⬝ a) w → Whnf w →
    ∃ m v, m ≤ n ∧ StepsN m t v ∧ Whnf v := by
  intro n
  induction n with
  | zero =>
    intro t a w hw ww
    cases hw
    exact ⟨0, t, Nat.le_refl 0, .refl t, whnf_fn ww⟩
  | succ n ih =>
    intro t a w hw ww
    cases progress t with
    | inl ht => exact ⟨0, t, Nat.zero_le _, .refl t, ht⟩
    | inr hs =>
      obtain ⟨t', s⟩ := hs
      cases hw with
      | step s' hw' =>
        have e := Step.det s' (Step.left a s)
        subst e
        obtain ⟨m, v, hm, hv, wv⟩ := ih hw' ww
        exact ⟨m + 1, v, Nat.succ_le_succ hm, .step s hv, wv⟩

-- ---------------------------------------------------------------------------
-- The head length
-- ---------------------------------------------------------------------------

/-- `t` reaches a weak head normal form in exactly `n` contractions. -/
def HLen (t : Term) (n : Nat) : Prop := ∃ w, StepsN n t w ∧ Whnf w

theorem hlen_of_eval {t v : Term} (h : Eval t v) : ∃ n, HLen t n :=
  let ⟨n, hn⟩ := steps_counted h.1
  ⟨n, v, hn, h.2⟩

theorem HLen.eval {t : Term} {n : Nat} (h : HLen t n) : ∃ v, Eval t v :=
  let ⟨w, hw, ww⟩ := h
  ⟨w, hw.steps, ww⟩

/-- A head reduction of `j` steps leaves exactly `n - j`. -/
theorem hlen_steps : ∀ {j : Nat} {t u : Term}, StepsN j t u → ∀ {n : Nat}, HLen t n →
    j ≤ n ∧ HLen u (n - j)
  | _, _, _, .refl _, n, h => ⟨Nat.zero_le n, by simpa using h⟩
  | _, _, _, .step s hs, n, ⟨w, hw, ww⟩ => by
    obtain ⟨m, rfl, hm⟩ := StepsN.after_step s hw ww
    obtain ⟨hj, hu⟩ := hlen_steps hs ⟨w, hm, ww⟩
    exact ⟨Nat.succ_le_succ hj, by simpa [Nat.succ_sub_succ] using hu⟩

/-- A weak reduction leaves at most `n`. -/
theorem hlen_wsteps {t u : Term} (h : WSteps t u) {n : Nat} (hn : HLen t n) :
    ∃ m, m ≤ n ∧ HLen u m :=
  let ⟨_, hw, ww⟩ := hn
  let ⟨m, w', hm, hs, hw'⟩ := StepsN.wtail h hw ww
  ⟨m, hm, w', hs, hw'⟩

/-- If `t ⬝ a` normalizes, `t` does, in no more steps. -/
theorem hlen_app {t a : Term} {n : Nat} (h : HLen (t ⬝ a) n) : ∃ m, m ≤ n ∧ HLen t m :=
  let ⟨_, hw, ww⟩ := h
  let ⟨m, v, hm, hv, wv⟩ := StepsN.app_left hw ww
  ⟨m, hm, v, hv, wv⟩

/-- A bound through a weak reduction: what bounds the reduct's head length
    bounds the term's. -/
theorem le_of_wsteps {t u : Term} {k : Nat} (h : WSteps t u) (ih : ∀ {N}, HLen u N → k ≤ N)
    {N : Nat} (hN : HLen t N) : k ≤ N :=
  let ⟨_, hM, hu⟩ := hlen_wsteps h hN
  Nat.le_trans (ih hu) hM

-- ---------------------------------------------------------------------------
-- Symbolic head reduction with a count
-- ---------------------------------------------------------------------------

/-- Head-reduce an open term for at most `n` steps (lean-ski's `ostep?`,
    stuck at a variable or an under-applied combinator), with the count. -/
def hred : Nat → OTerm → OTerm × Nat
  | 0, t => (t, 0)
  | n + 1, t =>
    match ostep? t with
    | none => (t, 0)
    | some t' =>
      let r := hred n t'
      (r.1, r.2 + 1)

/-- Each symbolic head step closes to a head step. -/
theorem hred_stepsN : ∀ (n : Nat) (t : OTerm) (σ : Nat → Term),
    StepsN (hred n t).2 (t.close σ) ((hred n t).1.close σ)
  | 0, t, σ => .refl _
  | n + 1, t, σ => by
    cases h : ostep? t with
    | none => simp only [hred, h]; exact .refl _
    | some t' =>
      simp only [hred, h]
      exact .step ((ostep?_sound h).close σ) (hred_stepsN n t' σ)

/-- `u` is the variable `i` applied to `k` arguments. -/
def headedBy (i : Nat) : Nat → OTerm → Bool
  | 0, .var j => i == j
  | k + 1, f ⬝ₒ _ => headedBy i k f
  | _, _ => false

/-- A term headed by `σ i` bounds the head length of `σ i`. -/
theorem hlen_headed : ∀ {k : Nat} {u : OTerm} {i : Nat}, headedBy i k u = true →
    ∀ (σ : Nat → Term) {N : Nat}, HLen (u.close σ) N → ∃ M, M ≤ N ∧ HLen (σ i) M
  | 0, .var j, i, h, σ, N, hN => by
    have e : i = j := by simpa [headedBy] using h
    subst e
    exact ⟨N, Nat.le_refl N, hN⟩
  | k + 1, f ⬝ₒ x, i, h, σ, N, hN => by
    have hf : headedBy i k f = true := by simpa [headedBy] using h
    obtain ⟨M1, hM1, h1⟩ := hlen_app (show HLen (f.close σ ⬝ x.close σ) N from hN)
    obtain ⟨M, hM, h2⟩ := hlen_headed hf σ h1
    exact ⟨M, Nat.le_trans hM hM1, h2⟩
  | 0, .S, _, h, _, _, _ => by simp [headedBy] at h
  | 0, .K, _, h, _, _, _ => by simp [headedBy] at h
  | 0, .I, _, h, _, _, _ => by simp [headedBy] at h
  | 0, _ ⬝ₒ _, _, h, _, _, _ => by simp [headedBy] at h
  | _ + 1, .S, _, h, _, _, _ => by simp [headedBy] at h
  | _ + 1, .K, _, h, _, _, _ => by simp [headedBy] at h
  | _ + 1, .I, _, h, _, _, _ => by simp [headedBy] at h
  | _ + 1, .var _, _, h, _, _, _ => by simp [headedBy] at h

/-- The check for a pending operand: the head reduction of `t` takes at
    least one step and ends headed by the variable `i` with `k` arguments. -/
def pendCheck (fuel : Nat) (t : OTerm) (i k : Nat) : Bool :=
  let r := hred fuel t
  r.2 != 0 && headedBy i k r.1

/-- A passed `pendCheck` bounds `σ i`'s head length strictly below `t`'s. -/
theorem pendCheck_sound {fuel i k : Nat} {t : OTerm} (h : pendCheck fuel t i k = true)
    (σ : Nat → Term) {N : Nat} (hN : HLen (t.close σ) N) : ∃ M, M < N ∧ HLen (σ i) M := by
  simp only [pendCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hj, hh⟩ := h
  obtain ⟨hle, hu⟩ := hlen_steps (hred_stepsN fuel t σ) hN
  obtain ⟨M, hM, hi⟩ := hlen_headed hh σ hu
  exact ⟨M, by omega, hi⟩

/-- The check for a forced value: the head reduction of `t` takes at least
    one step and ends as the variable `i` applied to one argument whose
    weak normal form is `target`. -/
def contCheck (fuel : Nat) (t : OTerm) (i : Nat) (target : OTerm) : Bool :=
  match hred fuel t with
  | (.var j ⬝ₒ e, n) => n != 0 && i == j && BitArith.wnf fuel e == target
  | _ => false

/-- A passed `contCheck` bounds `σ i ⬝ target` strictly below `t`. -/
theorem contCheck_sound {fuel i : Nat} {t target : OTerm} (h : contCheck fuel t i target = true)
    (σ : Nat → Term) {N : Nat} (hN : HLen (t.close σ) N) :
    ∃ M, M < N ∧ HLen (σ i ⬝ target.close σ) M := by
  unfold contCheck at h
  split at h
  · rename_i j e n heq
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    obtain ⟨⟨hn, hij⟩, hw⟩ := h
    subst hij
    have hs := hred_stepsN fuel t σ
    rw [heq] at hs
    obtain ⟨hle, hu⟩ := hlen_steps hs hN
    have hu' : HLen (σ i ⬝ e.close σ) (N - n) := hu
    obtain ⟨M, hM, h2⟩ := hlen_wsteps (WSteps.right _ (BitArith.run hw σ)) hu'
    exact ⟨M, by omega, h2⟩
  · cases h

-- ---------------------------------------------------------------------------
-- The primitives' head reductions
-- ---------------------------------------------------------------------------

theorem force_pend_chk : pendCheck 400 (forceT.toO ⬝ₒ .var 0 ⬝ₒ .var 1) 0 4 = true := by
  decide +kernel
theorem force_atom_chk :
    contCheck 400 (forceT.toO ⬝ₒ atomO (.var 0) ⬝ₒ .var 1) 1 (atomO (.var 0)) = true := by
  decide +kernel
theorem force_cell_chk :
    contCheck 400 (forceT.toO ⬝ₒ cellO (.var 0) (.var 1) ⬝ₒ .var 2) 2 (cellO (.var 0) (.var 1)) =
      true := by
  decide +kernel
theorem force_form_chk :
    contCheck 400 (forceT.toO ⬝ₒ formO (.var 0) (.var 1) (.var 2) ⬝ₒ .var 3) 3
      (formO (.var 0) (.var 1) (.var 2)) = true := by
  decide +kernel
theorem cel_pend_chk : pendCheck 400 (celT.toO ⬝ₒ .var 0) 0 4 = true := by decide +kernel
theorem inc_pend_chk : pendCheck 400 (incT.toO ⬝ₒ .var 0) 0 4 = true := by decide +kernel
theorem ifn_pend_chk : pendCheck 400 (ifnT.toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2) 0 4 = true := by
  decide +kernel
theorem ifn_zero_chk : pendCheck 400 (ifnT.toO ⬝ₒ atomO .K ⬝ₒ .var 1 ⬝ₒ .var 2) 1 0 = true := by
  decide +kernel
theorem ifn_one_chk :
    pendCheck 400 (ifnT.toO ⬝ₒ atomO (BitArith.consO BitArith.ttO .K) ⬝ₒ .var 1 ⬝ₒ .var 2) 2 0 =
      true := by
  decide +kernel
theorem eqn_pend_chk : pendCheck 400 (eqnFix.toO ⬝ₒ .var 0 ⬝ₒ .var 1) 0 4 = true := by
  decide +kernel

/-- A closing from a list, `K` past its end. -/
def envL (ts : List Term) : Nat → Term := fun i => ts.getD i K

/-- **`force` on a pending operand**: the operand's head length is strictly
    below the node's. -/
theorem hlen_force_pend {X k : Term} {N : Nat} (h : HLen (forceT ⬝ X ⬝ k) N) :
    ∃ M, M < N ∧ HLen X M := by
  have e : (forceT.toO ⬝ₒ .var 0 ⬝ₒ .var 1).close (envL [X, k]) = forceT ⬝ X ⬝ k := by
    simp [OTerm.close, close_toO, envL]
  rw [← e] at h
  exact pendCheck_sound force_pend_chk (envL [X, k]) h

theorem hlen_cel_pend {X : Term} {N : Nat} (h : HLen (celT ⬝ X) N) : ∃ M, M < N ∧ HLen X M := by
  have e : (celT.toO ⬝ₒ .var 0).close (envL [X]) = celT ⬝ X := by
    simp [OTerm.close, close_toO, envL]
  rw [← e] at h
  exact pendCheck_sound cel_pend_chk (envL [X]) h

theorem hlen_inc_pend {X : Term} {N : Nat} (h : HLen (incT ⬝ X) N) : ∃ M, M < N ∧ HLen X M := by
  have e : (incT.toO ⬝ₒ .var 0).close (envL [X]) = incT ⬝ X := by
    simp [OTerm.close, close_toO, envL]
  rw [← e] at h
  exact pendCheck_sound inc_pend_chk (envL [X]) h

theorem hlen_ifn_pend {X Y Z : Term} {N : Nat} (h : HLen (ifnT ⬝ X ⬝ Y ⬝ Z) N) :
    ∃ M, M < N ∧ HLen X M := by
  have e : (ifnT.toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ .var 2).close (envL [X, Y, Z]) = ifnT ⬝ X ⬝ Y ⬝ Z := by
    simp [OTerm.close, close_toO, envL]
  rw [← e] at h
  exact pendCheck_sound ifn_pend_chk (envL [X, Y, Z]) h

/-- **`ifn` on `0`** reaches its first branch in at least one step. -/
theorem hlen_ifn_zero {Y Z : Term} {N : Nat} (h : HLen (ifnT ⬝ encNoun (.atom 0) ⬝ Y ⬝ Z) N) :
    ∃ M, M < N ∧ HLen Y M := by
  have e : (ifnT.toO ⬝ₒ atomO .K ⬝ₒ .var 1 ⬝ₒ .var 2).close (envL [K, Y, Z]) =
      ifnT ⬝ encNoun (.atom 0) ⬝ Y ⬝ Z := by
    rw [encNoun_atom, bits_zero]
    simp [OTerm.close, close_toO, close_atomO, envL]
    rfl
  rw [← e] at h
  exact pendCheck_sound ifn_zero_chk (envL [K, Y, Z]) h

/-- **`ifn` on `1`** reaches its second branch in at least one step. -/
theorem hlen_ifn_one {Y Z : Term} {N : Nat} (h : HLen (ifnT ⬝ encNoun (.atom 1) ⬝ Y ⬝ Z) N) :
    ∃ M, M < N ∧ HLen Z M := by
  have e : (ifnT.toO ⬝ₒ atomO (BitArith.consO BitArith.ttO .K) ⬝ₒ .var 1 ⬝ₒ .var 2).close
      (envL [K, Y, Z]) = ifnT ⬝ encNoun (.atom 1) ⬝ Y ⬝ Z := by
    rw [encNoun_atom, bits_one]
    simp [OTerm.close, close_toO, close_atomO, envL]
    rfl
  rw [← e] at h
  exact pendCheck_sound ifn_one_chk (envL [K, Y, Z]) h

/-- **`eqn`** forces its first argument. -/
theorem hlen_eqn_pend {a b : Term} {N : Nat} (h : HLen (eqnFix ⬝ a ⬝ b) N) :
    ∃ M, M < N ∧ HLen a M := by
  have e : (eqnFix.toO ⬝ₒ .var 0 ⬝ₒ .var 1).close (envL [a, b]) = eqnFix ⬝ a ⬝ b := by
    simp [OTerm.close, close_toO, envL]
  rw [← e] at h
  exact pendCheck_sound eqn_pend_chk (envL [a, b]) h

/-- **`force` on an encoding** hands it to the continuation in at least one
    step: the continuation's head length is strictly below the node's. -/
theorem hlen_force_enc {r : Noun} {e k : Term} (he : Enc r e) {N : Nat}
    (h : HLen (forceT ⬝ e ⬝ k) N) : ∃ M, M < N ∧ HLen (k ⬝ e) M := by
  cases he with
  | atom n =>
    rw [encNoun_atom] at h ⊢
    have e : (forceT.toO ⬝ₒ atomO (.var 0) ⬝ₒ .var 1).close (envL [bitsT (bits n), k]) =
        forceT ⬝ atomT (bitsT (bits n)) ⬝ k := by
      simp [OTerm.close, close_toO, close_atomO, envL]
    rw [← e] at h
    have := contCheck_sound force_atom_chk (envL [bitsT (bits n), k]) h
    simpa [close_atomO, OTerm.close, envL] using this
  | @cell _ _ eh et _ _ =>
    have e : (forceT.toO ⬝ₒ cellO (.var 0) (.var 1) ⬝ₒ .var 2).close (envL [eh, et, k]) =
        forceT ⬝ cellT eh et ⬝ k := by
      simp [OTerm.close, close_toO, close_cellO, envL]
    rw [← e] at h
    have := contCheck_sound force_cell_chk (envL [eh, et, k]) h
    simpa [close_cellO, OTerm.close, envL] using this
  | @form h' t' eh et _ _ =>
    have e : (forceT.toO ⬝ₒ formO (.var 0) (.var 1) (.var 2) ⬝ₒ .var 3).close
        (envL [eh, et, nockToSki (.cell h' t'), k]) = forceT ⬝ formT eh et (nockToSki (.cell h' t')) ⬝ k := by
      simp [OTerm.close, close_toO, close_formO, envL]
    rw [← e] at h
    have := contCheck_sound force_form_chk (envL [eh, et, nockToSki (.cell h' t'), k]) h
    simpa [close_formO, OTerm.close, envL] using this

-- ---------------------------------------------------------------------------
-- Bounds through a weak reduction and one strict step
-- ---------------------------------------------------------------------------

/-- A pending operand under `force`: `t ↠ force X k` and `X`'s head length
    bounds `n`, so `t`'s bounds `n + 1`. -/
theorem le_force_pend {t X k : Term} {n : Nat} (h : WSteps t (forceT ⬝ X ⬝ k))
    (ih : ∀ {N}, HLen X N → n ≤ N) {N : Nat} (hN : HLen t N) : n + 1 ≤ N := by
  obtain ⟨N1, hN1, h1⟩ := hlen_wsteps h hN
  obtain ⟨M, hM, h2⟩ := hlen_force_pend h1
  have := ih h2
  omega

theorem le_cel_pend {t X : Term} {n : Nat} (h : WSteps t (celT ⬝ X))
    (ih : ∀ {N}, HLen X N → n ≤ N) {N : Nat} (hN : HLen t N) : n + 1 ≤ N := by
  obtain ⟨N1, hN1, h1⟩ := hlen_wsteps h hN
  obtain ⟨M, hM, h2⟩ := hlen_cel_pend h1
  have := ih h2
  omega

theorem le_inc_pend {t X : Term} {n : Nat} (h : WSteps t (incT ⬝ X))
    (ih : ∀ {N}, HLen X N → n ≤ N) {N : Nat} (hN : HLen t N) : n + 1 ≤ N := by
  obtain ⟨N1, hN1, h1⟩ := hlen_wsteps h hN
  obtain ⟨M, hM, h2⟩ := hlen_inc_pend h1
  have := ih h2
  omega

theorem le_ifn_pend {t X Y Z : Term} {n : Nat} (h : WSteps t (ifnT ⬝ X ⬝ Y ⬝ Z))
    (ih : ∀ {N}, HLen X N → n ≤ N) {N : Nat} (hN : HLen t N) : n + 1 ≤ N := by
  obtain ⟨N1, hN1, h1⟩ := hlen_wsteps h hN
  obtain ⟨M, hM, h2⟩ := hlen_ifn_pend h1
  have := ih h2
  omega

theorem le_ifn_zero {t Y Z : Term} {n : Nat} (h : WSteps t (ifnT ⬝ encNoun (.atom 0) ⬝ Y ⬝ Z))
    (ih : ∀ {N}, HLen Y N → n ≤ N) {N : Nat} (hN : HLen t N) : n + 1 ≤ N := by
  obtain ⟨N1, hN1, h1⟩ := hlen_wsteps h hN
  obtain ⟨M, hM, h2⟩ := hlen_ifn_zero h1
  have := ih h2
  omega

theorem le_ifn_one {t Y Z : Term} {n : Nat} (h : WSteps t (ifnT ⬝ encNoun (.atom 1) ⬝ Y ⬝ Z))
    (ih : ∀ {N}, HLen Z N → n ≤ N) {N : Nat} (hN : HLen t N) : n + 1 ≤ N := by
  obtain ⟨N1, hN1, h1⟩ := hlen_wsteps h hN
  obtain ⟨M, hM, h2⟩ := hlen_ifn_one h1
  have := ih h2
  omega

/-- A forced value: `t ↠ force e k` with `e` an encoding, `k ⬝ e ↠ u`, and
    `u`'s head length bounds `n`, so `t`'s bounds `n + 1`. -/
theorem le_force_enc {t e k u : Term} {r : Noun} {n : Nat} (h : WSteps t (forceT ⬝ e ⬝ k))
    (he : Enc r e) (hk : WSteps (k ⬝ e) u) (ih : ∀ {N}, HLen u N → n ≤ N) {N : Nat}
    (hN : HLen t N) : n + 1 ≤ N := by
  obtain ⟨N1, hN1, h1⟩ := hlen_wsteps h hN
  obtain ⟨M, hM, h2⟩ := hlen_force_enc he h1
  obtain ⟨M2, hM2, h3⟩ := hlen_wsteps hk h2
  have := ih h3
  omega

end Nock2Ski
