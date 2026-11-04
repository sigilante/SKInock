import Nock2Ski.DecLoopNorm

open Nock (Noun NockEval NT Outcome)
open Term

/-!
# The normalised loop's statement is sound

`nockloop_close` (`Nock2Ski/DecLoopNorm.lean`) turns an accepted proof of
the loop statement `nockLoopV f s p` into `replT W (normJ W) (checkT f s p)
↠ K`, `W = nockToSki decF`.  Here that is read as a Nock claim for the Λ loop
`decLoopF = Λ_N(while (top ≠ 0) dec)` on its subjects `[n [0 r]]`, by a
loop-specific route (no replacement lemma for arbitrary formulas).

- **Where the word sits.**  `W` is the autocons `S (S (K force) A0) (S (K
  consK) B0)` (`W_shape`), over 17661 nodes (`tsize_W`, through the inner
  loop's `pullK 2`).  Every combinator the loop's glue uses is smaller, so
  contains no `W` (`free_small`); the glue's nodes differ from `W` in their
  top levels (`neW`); the test's compiled formula, the axes and
  `encNoun x` for every noun are `W`-free (`free_test`, `free_encNoun`).
  The replacement therefore commutes with the compiler's shapes (`R6` …
  `R_auto`, `R_formT`), and the 13 occurrences in the compiled loop are the
  body's call site in `L`'s code and the codes of the `Form`s of the pinned
  literal `L` (the word's own literal among them).  Only `L`'s top `Form` is
  run (opcode 9); its replaced code is `Ct` (`C_eq`), the call site `normJ W`.
- **Forward** (`iter`, `loop_red`): by induction on `n`, the replaced loop on
  `[L' [n [0 r]]]` reaches an encoding of `[0 [0 r]]`, `normDec_enc` at each
  call.
- **Converse** (`check_eq`, `replaced_sound`): the replaced check is `eqn` of
  that run against `encNoun p`, so by Church–Rosser it reaches `K` only if `p
  = [0 [0 r]]`; **`nockloop_sound`** then gives `*[[n [0 r]] decLoopF] = p`
  (`decLoop_nock`).

The domain is exactly the subjects `[n [0 r]]` (any `n`, any `r`), on which the
loop terminates with a value.
-/

namespace Nock2Ski

namespace DecLoopSound

open DecNorm

local notation "v0" => OTerm.var 0

-- ---------------------------------------------------------------------------
-- Occurrences and sizes
-- ---------------------------------------------------------------------------

/-- The number of nodes. -/
def tsize : Term → Nat
  | .app f x => tsize f + tsize x + 1
  | _ => 1

/-- No subterm of `t` is `P`. -/
def NoOcc (P : Term) : Term → Prop
  | .app f x => Term.app f x ≠ P ∧ NoOcc P f ∧ NoOcc P x
  | .S => Term.S ≠ P
  | .K => Term.K ≠ P
  | .I => Term.I ≠ P

theorem replT_noOcc {P Q : Term} : ∀ {t : Term}, NoOcc P t → replT P Q t = t
  | .S, h | .K, h | .I, h => by simp only [replT]; rw [if_neg h]
  | .app f x, ⟨h, hf, hx⟩ => by
    simp only [replT]; rw [if_neg h, replT_noOcc hf, replT_noOcc hx]

theorem ne_of_tsize {t u : Term} (h : tsize t ≠ tsize u) : t ≠ u := fun e => h (e ▸ rfl)

theorem noOcc_of_lt {P : Term} : ∀ {t : Term}, tsize t < tsize P → NoOcc P t
  | .S, h | .K, h | .I, h => ne_of_tsize (Nat.ne_of_lt h)
  | .app f x, h => by
    refine ⟨ne_of_tsize (Nat.ne_of_lt h), noOcc_of_lt ?_, noOcc_of_lt ?_⟩ <;>
      simp only [tsize] at h <;> omega

theorem replT_app {P Q f x : Term} (h : Term.app f x ≠ P) :
    replT P Q (f ⬝ x) = replT P Q f ⬝ replT P Q x := by
  show (if Term.app f x = P then Q else _) = _
  rw [if_neg h]

-- ---------------------------------------------------------------------------
-- The compiler's shapes
-- ---------------------------------------------------------------------------

theorem abs_toO (t : Term) : abs 0 t.toO = .K ⬝ₒ t.toO := abs_of_not_mem (mem_toO 0 t)

theorem abs_at0 (t : Term) : abs 0 (t.toO ⬝ₒ v0) = t.toO := by
  rw [abs_app]
  simp [OTerm.mem, mem_toO]

theorem sh_auto (b c d : Noun) : nockToSki (.cell (.cell b c) d) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ nockToSki (.cell b c)) ⬝ (S ⬝ (K ⬝ consK) ⬝ nockToSki d) := by
  rw [nockToSki]
  simp [lamS, toTerm, absN, abs_app, at0, abs_toO, OTerm.mem, mem_toO, OTerm.close, close_toO]

macro "sh_tac" : tactic =>
  `(tactic| (rw [nockToSki]
             simp [lamS, toTerm, absN, abs_app, at0, abs_toO, OTerm.mem, mem_toO, OTerm.close, close_toO]))

theorem sh5 (b c : Noun) : nockToSki (.cell (.atom 5) (.cell b c)) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ nockToSki b) ⬝ (S ⬝ (K ⬝ eqK) ⬝ nockToSki c) := by sh_tac

theorem sh4 (b : Noun) : nockToSki (.cell (.atom 4) b) = S ⬝ (K ⬝ incT) ⬝ nockToSki b := by sh_tac

theorem sh6 (b c d : Noun) : nockToSki (.cell (.atom 6) (.cell b (.cell c d))) =
    S ⬝ (S ⬝ (S ⬝ (K ⬝ ifnT) ⬝ nockToSki b) ⬝ nockToSki c) ⬝ nockToSki d := by sh_tac

theorem sh7 (b c : Noun) : nockToSki (.cell (.atom 7) (.cell b c)) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ nockToSki b) ⬝ (K ⬝ nockToSki c) := by sh_tac

theorem sh8 (b c : Noun) : nockToSki (.cell (.atom 8) (.cell b c)) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ nockToSki b) ⬝ (pushK ⬝ nockToSki c) := by sh_tac

theorem sh9 (b c : Noun) : nockToSki (.cell (.atom 9) (.cell b c)) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ nockToSki c) ⬝ (K ⬝ pullK b) := by sh_tac

theorem sh1 (r : Noun) : nockToSki (.cell (.atom 1) r) = K ⬝ encLit r := by rw [nockToSki]

theorem axisPath_2 : axisPath 2 = [false] := by rw [axisPath_rec (by omega), axisPath_one]; rfl
theorem axisPath_3' : axisPath 3 = [true] := by rw [axisPath_rec (by omega), axisPath_one]; rfl
theorem axisPath_4 : axisPath 4 = [false, false] := by rw [axisPath_rec (by omega), axisPath_2]; rfl
theorem axisPath_5 : axisPath 5 = [false, true] := by rw [axisPath_rec (by omega), axisPath_2]; rfl
theorem axisPath_6 : axisPath 6 = [true, false] := by rw [axisPath_rec (by omega), axisPath_3']; rfl
theorem axisPath_7 : axisPath 7 = [true, true] := by rw [axisPath_rec (by omega), axisPath_3']; rfl

theorem pullK2_eq : pullK (.atom 2) = toTerm (absN [0] (appT.toO ⬝ₒ pickO v0 [false] ⬝ₒ v0)) := by
  rw [pullK, axisO.eq_def]; simp only [axisPath_2]

theorem tsize_pullK2 : tsize (pullK (.atom 2)) = 17661 := by rw [pullK2_eq]; decide +kernel

-- ---------------------------------------------------------------------------
-- The word, and its size
-- ---------------------------------------------------------------------------

/-- The word's head, `[7 [0 2] <guarded-dec>]`, compiled. -/
def A0 : Term := nockToSki (.cell (.atom 7) decHeadT)
/-- The word's tail, `[0 3]`, compiled. -/
def B0 : Term := nockToSki (.cell (.atom 0) (.atom 3))

/-- The word's top three levels: an autocons. -/
theorem W_shape : nockToSki decF = S ⬝ (S ⬝ (K ⬝ forceT) ⬝ A0) ⬝ (S ⬝ (K ⬝ consK) ⬝ B0) := by
  rw [decF_cells, sh_auto]; rfl

/-- The head holds the inner loop's `[9 2 0 1]`, so `pullK 2`. -/
theorem tsize_A0 : 17661 < tsize A0 := by
  simp only [A0, decHeadT, sh7, sh6, sh8, sh9, tsize, tsize_pullK2]; omega

theorem tsize_W : 17661 < tsize (nockToSki decF) := by
  rw [W_shape]; simp only [tsize]; have := tsize_A0; omega

/-- No occurrence of the compiled word. -/
@[irreducible] def Free (t : Term) : Prop := NoOcc (nockToSki decF) t

theorem free_def {t : Term} : Free t ↔ NoOcc (nockToSki decF) t := by unfold Free; rfl

theorem free_small {t : Term} (h : tsize t ≤ 17661) : Free t :=
  free_def.2 (noOcc_of_lt (by have := tsize_W; omega))

theorem free_app {f x : Term} (h : f ⬝ x ≠ nockToSki decF) (hf : Free f) (hx : Free x) : Free (f ⬝ x) :=
  free_def.2 ⟨h, free_def.1 hf, free_def.1 hx⟩

theorem free_S : Free S := free_small (by decide)
theorem free_K : Free K := free_small (by decide)
theorem free_I : Free I := free_small (by decide)
theorem free_forceT : Free forceT := free_small (by decide +kernel)
theorem free_consK : Free consK := free_small (by decide +kernel)
theorem free_pushK : Free pushK := free_small (by decide +kernel)
theorem free_ifnT : Free ifnT := free_small (by decide +kernel)
theorem free_eqK : Free eqK := free_small (by decide +kernel)
theorem free_incT : Free incT := free_small (by decide +kernel)
theorem free_eqnFix : Free eqnFix := free_small (by decide +kernel)
theorem free_pullK2 : Free (pullK (.atom 2)) := free_small (by rw [pullK2_eq]; decide +kernel)

theorem small_ne {t u : Term} (ht : tsize t ≤ 17661) (hu : 17661 < tsize u) : t ≠ u :=
  ne_of_tsize (by omega)

theorem pushK_ne : pushK ≠ S ⬝ (S ⬝ (K ⬝ forceT) ⬝ A0) :=
  small_ne (by decide +kernel) (by simp only [tsize]; have := tsize_A0; omega)
theorem eqnFix_ne : eqnFix ≠ S ⬝ (S ⬝ (K ⬝ forceT) ⬝ A0) :=
  small_ne (by decide +kernel) (by simp only [tsize]; have := tsize_A0; omega)
theorem eqnFix_ne_S : eqnFix ≠ S := ne_of_tsize (by decide +kernel)
theorem eqK_ne_consK : eqK ≠ consK := ne_of_tsize (by decide +kernel)
theorem ifnT_ne_forceT : ifnT ≠ forceT := ne_of_tsize (by decide +kernel)
theorem incT_ne_forceT : incT ≠ forceT := ne_of_tsize (by decide +kernel)
theorem pushK_ne_consK : pushK ≠ consK := ne_of_tsize (by decide +kernel)
theorem pushK_ne_SK : pushK ≠ S ⬝ (K ⬝ consK) := ne_of_tsize (by decide +kernel)

/-- A node is not the word: compare the top levels. -/
macro "neW" : tactic =>
  `(tactic| (rw [W_shape]; simp [pushK_ne, eqnFix_ne, eqnFix_ne_S, eqK_ne_consK, ifnT_ne_forceT, incT_ne_forceT, pushK_ne_consK, pushK_ne_SK]))

syntax "free_tac" : tactic
macro_rules
  | `(tactic| free_tac) => `(tactic| first
      | with_reducible assumption
      | with_reducible exact free_S
      | with_reducible exact free_K
      | with_reducible exact free_I
      | with_reducible exact free_forceT
      | with_reducible exact free_consK
      | with_reducible exact free_pushK
      | with_reducible exact free_ifnT
      | with_reducible exact free_eqK
      | with_reducible exact free_incT
      | with_reducible exact free_pullK2
      | (with_reducible refine free_app (by neW) ?_ ?_) <;> free_tac)

-- ---------------------------------------------------------------------------
-- Free compiled formulas
-- ---------------------------------------------------------------------------

theorem free_n0 (k : Nat) (bs : List Bool) (hp : axisPath (k + 1) = bs)
    (h : tsize (lamS (pickO v0 bs)) ≤ 17661) : Free (nockToSki (.cell (.atom 0) (.atom (k + 1)))) := by
  rw [nockToSki]; simp only [axisO, hp]; exact free_small h

theorem free01 : Free (nockToSki (.cell (.atom 0) (.atom 1))) := free_n0 0 [] axisPath_one (by decide +kernel)
theorem free02 : Free (nockToSki (.cell (.atom 0) (.atom 2))) := free_n0 1 _ axisPath_2 (by decide +kernel)
theorem free03 : Free (nockToSki (.cell (.atom 0) (.atom 3))) := free_n0 2 _ axisPath_3' (by decide +kernel)
theorem free04 : Free (nockToSki (.cell (.atom 0) (.atom 4))) := free_n0 3 _ axisPath_4 (by decide +kernel)
theorem free05 : Free (nockToSki (.cell (.atom 0) (.atom 5))) := free_n0 4 _ axisPath_5 (by decide +kernel)
theorem free06 : Free (nockToSki (.cell (.atom 0) (.atom 6))) := free_n0 5 _ axisPath_6 (by decide +kernel)
theorem free07 : Free (nockToSki (.cell (.atom 0) (.atom 7))) := free_n0 6 _ axisPath_7 (by decide +kernel)

theorem free4 {b : Noun} (hb : Free (nockToSki b)) : Free (nockToSki (.cell (.atom 4) b)) := by
  rw [sh4]; free_tac
theorem free5 {b c : Noun} (hb : Free (nockToSki b)) (hc : Free (nockToSki c)) :
    Free (nockToSki (.cell (.atom 5) (.cell b c))) := by
  rw [sh5]; free_tac
theorem free6 {b c d : Noun} (hb : Free (nockToSki b)) (hc : Free (nockToSki c)) (hd : Free (nockToSki d)) :
    Free (nockToSki (.cell (.atom 6) (.cell b (.cell c d)))) := by
  rw [sh6]; free_tac
theorem free7 {b c : Noun} (hb : Free (nockToSki b)) (hc : Free (nockToSki c)) :
    Free (nockToSki (.cell (.atom 7) (.cell b c))) := by
  rw [sh7]; free_tac
theorem free9_2 {c : Noun} (hc : Free (nockToSki c)) :
    Free (nockToSki (.cell (.atom 9) (.cell (.atom 2) c))) := by
  rw [sh9]; free_tac
theorem free_auto {b c d : Noun} (h1 : Free (nockToSki (.cell b c))) (h2 : Free (nockToSki d))
    (h3 : nockToSki (.cell b c) ≠ A0 ∨ nockToSki d ≠ B0) : Free (nockToSki (.cell (.cell b c) d)) := by
  rw [sh_auto]
  refine free_app ?_ (by free_tac) (by free_tac)
  intro hW; rw [W_shape] at hW
  simp only [Term.app.injEq, true_and] at hW
  exact h3.elim (fun h => h hW.1) (fun h => h hW.2)

theorem A0_shape : ∃ X Y, A0 = S ⬝ (S ⬝ (K ⬝ forceT) ⬝ X) ⬝ (K ⬝ Y) := by
  rw [A0, decHeadT, sh7]; exact ⟨_, _, rfl⟩

theorem ne_A0_small {t : Term} (h : tsize t ≤ 17661) : t ≠ A0 := small_ne h tsize_A0

/-- The loop's test, `over over eq ifte(over inc, over)`. -/
theorem NT_decTest : NT decTest =
    n! "[7 [[0 6] 0 1] 7 [[0 6] 0 1] 7 [[5 [0 6] 0 2] 0 7] 7 [6 [0 2] [7 [0 3] 7 [[0 6] 0 1] 7 [[4 0 2] 0 3] 0 1] 7 [0 3] 7 [[0 6] 0 1] 0 1] 0 1]" :=
  rfl

theorem free_over : Free (nockToSki (n! "[[0 6] 0 1]")) :=
  free_auto free06 free01 (.inl (ne_A0_small (by rw [nockToSki]; simp only [axisO, axisPath_6]; decide +kernel)))

theorem free_eq : Free (nockToSki (n! "[[5 [0 6] 0 2] 0 7]")) := by
  refine free_auto (free5 free06 free02) free07 (.inl ?_)
  obtain ⟨X, Y, e⟩ := A0_shape
  rw [e, sh5]; simp

theorem free_inc : Free (nockToSki (n! "[[4 0 2] 0 3]")) := by
  refine free_auto (free4 free02) free03 (.inl ?_)
  obtain ⟨X, Y, e⟩ := A0_shape
  rw [e, sh4]; simp

theorem free_test : Free (nockToSki (NT decTest)) := by
  rw [NT_decTest]
  exact free7 free_over (free7 free_over (free7 free_eq (free7 (free6 free02
    (free7 free03 (free7 free_over (free7 free_inc free01)))
    (free7 free03 (free7 free_over free01))) free01)))

theorem free_bl : ∀ bs : List Bool, Free (BitArith.bl bs)
  | [] => free_K
  | b :: bs => by
    have h1 := free_bl bs
    have h2 : Free (Compose.boolT b) := by cases b <;> simp only [Compose.boolT] <;> free_tac
    show Free (K ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ Compose.boolT b)) ⬝ (K ⬝ BitArith.bl bs)))
    free_tac

theorem free_encNoun : ∀ x : Noun, Free (encNoun x)
  | .atom n => by
    have h := free_bl (bits n)
    show Free (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ I ⬝ (K ⬝ BitArith.bl (bits n))))))
    free_tac
  | .cell h t => by
    have h1 := free_encNoun h
    have h2 := free_encNoun t
    show Free (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (S ⬝ I ⬝ (K ⬝ encNoun h)) ⬝ (K ⬝ encNoun t)))))
    free_tac

-- ---------------------------------------------------------------------------
-- The replacement, pushed through the compiled loop
-- ---------------------------------------------------------------------------

/-- Every occurrence of the compiled word replaced by the normalised one. -/
@[irreducible] def RW (t : Term) : Term := replT (nockToSki decF) (normJ (nockToSki decF)) t

theorem RW_def (t : Term) : RW t = replT (nockToSki decF) (normJ (nockToSki decF)) t := by unfold RW; rfl

theorem replT_self (P Q : Term) : replT P Q P = Q := by
  cases P <;> simp [replT]

theorem RW_app {f x : Term} (h : f ⬝ x ≠ nockToSki decF) : RW (f ⬝ x) = RW f ⬝ RW x := by
  simp only [RW_def]; exact replT_app h
theorem RW_free {t : Term} (h : Free t) : RW t = t := by rw [RW_def]; exact replT_noOcc (free_def.1 h)
theorem RW_W : RW (nockToSki decF) = normJ (nockToSki decF) := by rw [RW_def]; exact replT_self _ _

theorem RW_S : RW S = S := RW_free free_S
theorem RW_K : RW K = K := RW_free free_K
theorem RW_I : RW I = I := RW_free free_I
theorem RW_forceT : RW forceT = forceT := RW_free free_forceT
theorem RW_consK : RW consK = consK := RW_free free_consK
theorem RW_pushK : RW pushK = pushK := RW_free free_pushK
theorem RW_ifnT : RW ifnT = ifnT := RW_free free_ifnT
theorem RW_pullK2 : RW (pullK (.atom 2)) = pullK (.atom 2) := RW_free free_pullK2

macro "push_tac" : tactic =>
  `(tactic| simp (disch := neW) only [RW_app, RW_S, RW_K, RW_I, RW_forceT, RW_consK, RW_pushK, RW_ifnT,
    RW_pullK2])

theorem R6 (b c d : Noun) : RW (nockToSki (.cell (.atom 6) (.cell b (.cell c d)))) =
    S ⬝ (S ⬝ (S ⬝ (K ⬝ ifnT) ⬝ RW (nockToSki b)) ⬝ RW (nockToSki c)) ⬝ RW (nockToSki d) := by
  rw [sh6]; push_tac

theorem R7 (b c : Noun) : RW (nockToSki (.cell (.atom 7) (.cell b c))) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ RW (nockToSki b)) ⬝ (K ⬝ RW (nockToSki c)) := by
  rw [sh7]; push_tac

theorem R8 (b c : Noun) : RW (nockToSki (.cell (.atom 8) (.cell b c))) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ RW (nockToSki b)) ⬝ (pushK ⬝ RW (nockToSki c)) := by
  rw [sh8]; push_tac

theorem R9_2 (c : Noun) : RW (nockToSki (.cell (.atom 9) (.cell (.atom 2) c))) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ RW (nockToSki c)) ⬝ (K ⬝ pullK (.atom 2)) := by
  rw [sh9]; push_tac

theorem R1 (r : Noun) : RW (nockToSki (.cell (.atom 1) r)) = K ⬝ RW (encLit r) := by
  rw [sh1]; push_tac

theorem R_auto {b c d : Noun} (h3 : nockToSki (.cell b c) ≠ A0 ∨ nockToSki d ≠ B0) :
    RW (nockToSki (.cell (.cell b c) d)) =
      S ⬝ (S ⬝ (K ⬝ forceT) ⬝ RW (nockToSki (.cell b c))) ⬝ (S ⬝ (K ⬝ consK) ⬝ RW (nockToSki d)) := by
  rw [sh_auto]
  have h : S ⬝ (S ⬝ (K ⬝ forceT) ⬝ nockToSki (.cell b c)) ⬝ (S ⬝ (K ⬝ consK) ⬝ nockToSki d) ≠ nockToSki decF := by
    intro hW; rw [W_shape] at hW
    simp only [Term.app.injEq, true_and] at hW
    exact h3.elim (fun h => h hW.1) (fun h => h hW.2)
  rw [RW_app h]; push_tac

theorem R_formT (h t k : Term) : RW (formT h t k) = formT (RW h) (RW t) (RW k) := by
  simp only [formT, Compose.pairT]; push_tac

-- ---------------------------------------------------------------------------
-- The compiled loop, replaced
-- ---------------------------------------------------------------------------

/-- `L`'s test half, `[7 [0 3] Λ_N(test)]`. -/
local notation "T7" => Noun.cell (Noun.atom 7) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 3)) (NT decTest))
/-- The body, `Λ_N(dec)`, `[7 decF [0 1]]`. -/
local notation "NTb" => Noun.cell (Noun.atom 7) (Noun.cell decF (Noun.cell (Noun.atom 0) (Noun.atom 1)))
local notation "Qa" => Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 6)) (Noun.cell (Noun.atom 7) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 5)) NTb))
local notation "Q6" => Noun.cell (Noun.atom 6) (Noun.cell (Noun.cell (Noun.atom 0) (Noun.atom 4))
  (Noun.cell (Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom 2) Qa)) (Noun.cell (Noun.atom 0) (Noun.atom 5))))
/-- The loop body `L` that `Λ_N(while …)` pins. -/
local notation "Lc" => Noun.cell (Noun.atom 8) (Noun.cell T7 Q6)
local notation "NwN" => Noun.cell (Noun.atom 8) (Noun.cell (Noun.cell (Noun.atom 1) Lc)
  (Noun.cell (Noun.atom 9) (Noun.cell (Noun.atom 2) (Noun.cell (Noun.atom 0) (Noun.atom 1)))))

theorem Lwhile_eq : Nock.Lwhile decTest (.seq .dec .nil) = Lc := rfl
theorem decLoopF_eq : decLoopF = .cell (Noun.atom 7) (Noun.cell NwN (Noun.cell (Noun.atom 0) (Noun.atom 1))) := rfl

local notation "N0" n => nockToSki (Noun.cell (Noun.atom 0) (Noun.atom n))

/-- The normalised word. -/
def Jn : Term := normJ (nockToSki decF)
def Bd : Term := S ⬝ (S ⬝ (K ⬝ forceT) ⬝ Jn) ⬝ (K ⬝ N0 1)
def Qbt : Term := S ⬝ (S ⬝ (K ⬝ forceT) ⬝ N0 5) ⬝ (K ⬝ Bd)
def Qat : Term := S ⬝ (S ⬝ (K ⬝ forceT) ⬝ N0 6) ⬝ (S ⬝ (K ⬝ consK) ⬝ Qbt)
def Q9t : Term := S ⬝ (S ⬝ (K ⬝ forceT) ⬝ Qat) ⬝ (K ⬝ pullK (.atom 2))
def Q6t : Term := S ⬝ (S ⬝ (S ⬝ (K ⬝ ifnT) ⬝ N0 4) ⬝ Q9t) ⬝ N0 5
/-- `L`'s code with the word replaced. -/
def Ct : Term := S ⬝ (S ⬝ (K ⬝ forceT) ⬝ nockToSki T7) ⬝ (pushK ⬝ Q6t)

theorem n06_ne_A0 : (N0 6) ≠ A0 :=
  ne_A0_small (by rw [nockToSki]; simp only [axisO, axisPath_6]; decide +kernel)

theorem C_eq : RW (nockToSki Lc) = Ct := by
  rw [R8, RW_free (free7 free03 free_test), R6, RW_free free04, RW_free free05, R9_2, R_auto (.inl n06_ne_A0),
    RW_free free06, R7, RW_free free05, R7, RW_W, RW_free free01]
  rfl

/-- The pinned `L`, replaced: a `Form` whose code is `Ct`. -/
def Xt : Term := RW (encLit Lc)

theorem X_eq : Xt = formT (RW (encLit (.atom 8))) (RW (encLit (.cell T7 Q6))) Ct := by
  unfold Xt
  conv => lhs; rw [encLit]
  rw [if_pos (by decide), R_formT, C_eq]

theorem forceX (k : Term) : WSteps (forceT ⬝ Xt ⬝ k) (k ⬝ Xt) := by
  rw [X_eq]; exact force_form _ _ _ _

theorem appX (x : Term) : WSteps (appT ⬝ Xt ⬝ x) (Ct ⬝ x) := by
  rw [X_eq]; exact app_form _ _ _ _

-- ---------------------------------------------------------------------------
-- Running it
-- ---------------------------------------------------------------------------

theorem ex_SK1 (a X s : Term) : WSteps (S ⬝ (K ⬝ a) ⬝ X ⬝ s) (a ⬝ (X ⬝ s)) :=
  (WSteps.single (.S _ _ _)).trans (WSteps.left _ (WSteps.single (.K _ _)))

theorem ex_SK (a X Y s : Term) : WSteps (S ⬝ (S ⬝ (K ⬝ a) ⬝ X) ⬝ Y ⬝ s) (a ⬝ (X ⬝ s) ⬝ (Y ⬝ s)) :=
  (WSteps.single (.S _ _ _)).trans (WSteps.left _ (ex_SK1 a X s))

theorem ex_SSK (a X Y Z s : Term) :
    WSteps (S ⬝ (S ⬝ (S ⬝ (K ⬝ a) ⬝ X) ⬝ Y) ⬝ Z ⬝ s) (a ⬝ (X ⬝ s) ⬝ (Y ⬝ s) ⬝ (Z ⬝ s)) :=
  (WSteps.single (.S _ _ _)).trans (WSteps.left _ (ex_SK a X Y s))

theorem n01_red (e : Term) : WSteps ((N0 1) ⬝ e) e := by
  have := step_op0 0 e; rw [axisPath_one] at this; exact this

theorem n03_red (h t : Term) : WSteps ((N0 3) ⬝ cellT h t) t := by
  have := step_op0 2 (cellT h t); rw [axisPath_3'] at this; exact this.trans (tl_cellT _ _)

theorem n04_red (s : Term) : WSteps ((N0 4) ⬝ s) (hdT ⬝ (hdT ⬝ s)) := by
  have := step_op0 3 s; rw [axisPath_4] at this; exact this

theorem n05_red (s : Term) : WSteps ((N0 5) ⬝ s) (tlT ⬝ (hdT ⬝ s)) := by
  have := step_op0 4 s; rw [axisPath_5] at this; exact this

theorem n06_red (s : Term) : WSteps ((N0 6) ⬝ s) (hdT ⬝ (tlT ⬝ s)) := by
  have := step_op0 5 s; rw [axisPath_6] at this; exact this

theorem pull2_red (h t : Term) : WSteps (pullK (.atom 2) ⬝ cellT h t) (appT ⬝ h ⬝ cellT h t) := by
  have := pullK_succ 1 (cellT h t); rw [axisPath_2] at this
  exact this.trans (WSteps.left _ (WSteps.right _ (hd_cellT _ _)))

/-- The test half on `[L stack]`: the test's value on the stack. -/
theorem T7_red {s v : Noun} {es : Term} (hes : Enc s es) (ht : NockEval s (NT decTest) (.val v)) :
    ∃ e1, Enc v e1 ∧ WSteps (nockToSki T7 ⬝ cellT Xt es) e1 := by
  obtain ⟨e1, he1, hr⟩ := embed_value ht hes
  exact ⟨e1, he1, (step_op7 _ _ _).trans ((WSteps.left _ (WSteps.right _ (n03_red _ _))).trans
    ((force_enc hes _).trans hr))⟩

/-- `L`'s code up to its branch: the test's value pushed. -/
theorem pre_red {v : Noun} {e1 es : Term} (he1 : Enc v e1) (hr : WSteps (nockToSki T7 ⬝ cellT Xt es) e1) :
    WSteps (Ct ⬝ cellT Xt es) (ifnT ⬝ ((N0 4) ⬝ cellT e1 (cellT Xt es)) ⬝ (Q9t ⬝ cellT e1 (cellT Xt es)) ⬝
      ((N0 5) ⬝ cellT e1 (cellT Xt es))) := by
  have h1 : WSteps (Ct ⬝ cellT Xt es) (Q6t ⬝ cellT e1 (cellT Xt es)) :=
    (ex_SK _ _ _ _).trans ((WSteps.left _ (WSteps.right _ hr)).trans ((force_enc he1 _).trans
      ((pushK_beta _ _ _).trans (WSteps.right _ (CellC_red _ _)))))
  exact h1.trans (ex_SSK _ _ _ _ _)

/-- **The loop on `[L [n [0 r]]]`**: an encoding of `[0 [0 r]]`. -/
theorem iter (r : Noun) : ∀ (n : Nat) (es : Term), Enc (.cell (.atom n) (.cell (.atom 0) r)) es →
    ∃ e, Enc (.cell (.atom 0) (.cell (.atom 0) r)) e ∧ WSteps (Ct ⬝ cellT Xt es) e := by
  intro n
  induction n with
  | zero =>
    intro es hes
    obtain ⟨e1, he1, hr⟩ := T7_red hes ((Nock.composition_term _ _ _).2 (decTest_zero r))
    obtain ⟨ef, hef, hfr⟩ := hd_enc he1
    obtain ⟨et, het, htr⟩ := tl_enc he1
    have h4 := (n04_red (cellT e1 (cellT Xt es))).trans ((WSteps.right _ (hd_cellT _ _)).trans hfr)
    have h5 := (n05_red (cellT e1 (cellT Xt es))).trans ((WSteps.right _ (hd_cellT _ _)).trans htr)
    refine ⟨et, het, (pre_red he1 hr).trans ?_⟩
    exact (WSteps.left _ (WSteps.left _ (WSteps.right _ h4))).trans ((ifn_enc_one hef _ _).trans h5)
  | succ k ih =>
    intro es hes
    obtain ⟨e1, he1, hr⟩ := T7_red hes ((Nock.composition_term _ _ _).2 (decTest_succ k r))
    obtain ⟨ef, hef, hfr⟩ := hd_enc he1
    obtain ⟨et, het, htr⟩ := tl_enc he1
    have h4 := (n04_red (cellT e1 (cellT Xt es))).trans ((WSteps.right _ (hd_cellT _ _)).trans hfr)
    have h5 := (n05_red (cellT e1 (cellT Xt es))).trans ((WSteps.right _ (hd_cellT _ _)).trans htr)
    have h6 := (n06_red (cellT e1 (cellT Xt es))).trans ((WSteps.right _ (tl_cellT _ _)).trans (hd_cellT _ _))
    -- the body: the normalised word on the stack
    have hd : WSteps (normJ (nockToSki decF) ⬝ et) (encNoun (.cell (.atom k) (.cell (.atom 0) r))) :=
      normDec_enc het
    have hB : WSteps (Bd ⬝ et) (encNoun (.cell (.atom k) (.cell (.atom 0) r))) :=
      (ex_SK _ _ _ _).trans ((WSteps.left _ (WSteps.right _ hd)).trans
        ((WSteps.right _ (WSteps.single (.K _ _))).trans ((force_spec _ _).trans (n01_red _))))
    have hQb : WSteps (Qbt ⬝ cellT e1 (cellT Xt es)) (encNoun (.cell (.atom k) (.cell (.atom 0) r))) :=
      (ex_SK _ _ _ _).trans ((WSteps.left _ (WSteps.right _ h5)).trans
        ((WSteps.right _ (WSteps.single (.K _ _))).trans ((force_enc het _).trans hB)))
    have hQa : WSteps (Qat ⬝ cellT e1 (cellT Xt es)) (cellT Xt (encNoun (.cell (.atom k) (.cell (.atom 0) r)))) :=
      (ex_SK _ _ _ _).trans ((WSteps.left _ (WSteps.right _ h6)).trans
        ((WSteps.right _ (ex_SK1 _ _ _)).trans ((forceX _).trans ((consK_beta _ _).trans
          ((WSteps.left _ (WSteps.right _ hQb)).trans ((force_spec _ _).trans (CellC_red _ _)))))))
    have hQ9 : WSteps (Q9t ⬝ cellT e1 (cellT Xt es)) (Ct ⬝ cellT Xt (encNoun (.cell (.atom k) (.cell (.atom 0) r)))) :=
      (ex_SK _ _ _ _).trans ((WSteps.right _ (WSteps.single (.K _ _))).trans
        ((WSteps.left _ (WSteps.right _ hQa)).trans ((force_cellT _ _ _).trans ((pull2_red _ _).trans (appX _)))))
    obtain ⟨e, he, hre⟩ := ih _ (enc_encNoun _)
    refine ⟨e, he, (pre_red he1 hr).trans ?_⟩
    exact (WSteps.left _ (WSteps.left _ (WSteps.right _ h4))).trans ((ifn_enc_zero hef _ _).trans (hQ9.trans hre))

theorem RW_F : RW (nockToSki decLoopF) =
    S ⬝ (S ⬝ (K ⬝ forceT) ⬝ (S ⬝ (S ⬝ (K ⬝ forceT) ⬝ (K ⬝ Xt)) ⬝
      (pushK ⬝ nockToSki (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 0) (.atom 1))))))) ⬝ (K ⬝ N0 1) := by
  rw [decLoopF_eq, R7, R8, R1, RW_free (free9_2 free01), RW_free free01]; rfl

/-- **The replaced loop on `[n [0 r]]`**: an encoding of `[0 [0 r]]`, the
    loop's Nock value. -/
theorem loop_red (n : Nat) (r : Noun) :
    ∃ e, Enc (.cell (.atom 0) (.cell (.atom 0) r)) e ∧
      WSteps (RW (nockToSki decLoopF) ⬝ encNoun (.cell (.atom n) (.cell (.atom 0) r))) e := by
  obtain ⟨e, he, hre⟩ := iter r n _ (enc_encNoun _)
  refine ⟨e, he, ?_⟩
  rw [RW_F]
  have hN : WSteps (S ⬝ (S ⬝ (K ⬝ forceT) ⬝ (K ⬝ Xt)) ⬝
      (pushK ⬝ nockToSki (.cell (.atom 9) (.cell (.atom 2) (.cell (.atom 0) (.atom 1))))) ⬝
      encNoun (.cell (.atom n) (.cell (.atom 0) r))) e :=
    (ex_SK _ _ _ _).trans ((WSteps.left _ (WSteps.right _ (WSteps.single (.K _ _)))).trans ((forceX _).trans
      ((pushK_beta _ _ _).trans ((WSteps.right _ (CellC_red _ _)).trans ((step_op9 _ _ _).trans
        ((WSteps.left _ (WSteps.right _ (n01_red _))).trans ((force_cellT _ _ _).trans
          ((pull2_red _ _).trans ((appX _).trans hre)))))))))
  exact (ex_SK _ _ _ _).trans ((WSteps.left _ (WSteps.right _ hN)).trans
    ((WSteps.right _ (WSteps.single (.K _ _))).trans ((force_enc he _).trans (n01_red _))))

-- ---------------------------------------------------------------------------
-- The converse
-- ---------------------------------------------------------------------------

/-- The replaced check is `eqn` of the replaced loop on the code-free
    subject against `encNoun p`: the word occurs nowhere else. -/
theorem check_eq (s p : Noun) :
    replT (nockToSki decF) (normJ (nockToSki decF)) (checkT decLoopF s p) =
      eqnFix ⬝ (RW (nockToSki decLoopF) ⬝ encNoun s) ⬝ encNoun p := by
  rw [← RW_def]
  have hF : nockToSki decLoopF = S ⬝ (S ⬝ (K ⬝ forceT) ⬝ nockToSki NwN) ⬝ (K ⬝ N0 1) := by
    rw [decLoopF_eq, sh7]
  have c1 : eqnFix ⬝ (nockToSki decLoopF ⬝ encNoun s) ⬝ encNoun p ≠ nockToSki decF := by rw [hF]; neW
  have c2 : eqnFix ⬝ (nockToSki decLoopF ⬝ encNoun s) ≠ nockToSki decF := by rw [hF]; neW
  have c3 : nockToSki decLoopF ⬝ encNoun s ≠ nockToSki decF := by rw [hF]; neW
  unfold checkT
  rw [RW_app c1, RW_app c2, RW_app c3, RW_free free_eqnFix, RW_free (free_encNoun s), RW_free (free_encNoun p)]

/-- **The replaced check reaching `K` fixes the product**: on `[n [0 r]]`
    it is `[0 [0 r]]`. -/
theorem replaced_sound {n : Nat} {r p : Noun}
    (hK : WSteps (replT (nockToSki decF) (normJ (nockToSki decF))
      (checkT decLoopF (.cell (.atom n) (.cell (.atom 0) r)) p)) K) :
    p = .cell (.atom 0) (.cell (.atom 0) r) := by
  rw [check_eq] at hK
  obtain ⟨e, he, hre⟩ := loop_red n r
  have h2 := (WSteps.left _ (WSteps.right _ hre)).trans (eqn_enc he (enc_encNoun p))
  have hb := (Compose.wsteps_K_iff h2).mp hK
  by_cases hq : Noun.cell (.atom 0) (.cell (.atom 0) r) = p
  · exact hq.symm
  · rw [decide_eq_false hq] at hb; exact absurd hb Compose.F_not_K

end DecLoopSound

open DecLoopSound in
/-- **`nockloop_sound`**: an accepted proof of the normalised loop's
    `decterm` statement for `*[[n [0 r]] decLoopF] = p` (the verifier
    `nockLoopV`, every occurrence of the compiled word `dec` replaced by
    `normJ` of the jet) is a Nock derivation of the claim. -/
theorem nockloop_sound {n : Nat} {r p : Noun} {W : Nat} {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs
      (Circuit.compDAirsG [nockLoopV decLoopF (.cell (.atom n) (.cell (.atom 0) r)) p] W) = true)
    (hacc : Circuit.AcceptedP Rs ts) :
    NockEval (.cell (.atom n) (.cell (.atom 0) r)) decLoopF (.val p) := by
  have hp := replaced_sound (nockloop_close hs hacc)
  subst hp
  exact decLoop_nock n r

end Nock2Ski
