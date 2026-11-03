import Nock2Ski.Basic

/-!
# Pending Nock runs: a derivation cut off after `n` steps

Milestone M4e of `PLAN.md`.  lean-nock's `Nock.Fuel` has the fuel
interpreter `nockF` and its completeness, but cannot be imported beside
lean-ski (`Nock.Fuel`'s root-level `Diverges` clashes with
`Ski.Basic`'s), so the partial run is stated here as an inductive
relation over `NockEval` alone.

`Pending n s f`: the evaluation of `f` on `s` is still running after `n`
costed steps.  Its constructors mirror the premises of `NockEval`'s
constructors: at each node one operand is pending and the operands before
it in lean-nock's order have values (`NockEval … (.val _)`).  Every
constructor costs one step except the static hint, which the compiler
erases (`nockToSki [11 t c] = nockToSki c`) and which cannot repeat
forever since it shrinks the formula.  `Pending 0 s f` always holds.

`pending_of_noOut`: if `f` on `s` has no outcome at all, it is pending at
every `n`.  By induction on `n` and, for the hint, on the formula: at a
node with no outcome, some operand has no outcome (an outcome of every
operand would give the node one), and that operand is the pending one.
-/

namespace Nock2Ski

open Noun

/-- No outcome: lean-nock's `Diverges` (`Nock/Fuel.lean`), restated. -/
def NoOut (s f : Noun) : Prop := ∀ o, ¬ NockEval s f o

/-- The run of `f` on `s` is still going after `n` costed steps. -/
inductive Pending : Nat → Noun → Noun → Prop
  | zero {s f} : Pending 0 s f
  -- autocons
  | autocons_L {n a b c d} : Pending n a (cell b c) → Pending (n + 1) a (cell (cell b c) d)
  | autocons_R {n a b c d r1} : NockEval a (cell b c) (.val r1) → Pending n a d →
      Pending (n + 1) a (cell (cell b c) d)
  -- 2
  | op2_b {n a b c} : Pending n a b → Pending (n + 1) a (cell (atom 2) (cell b c))
  | op2_c {n a b c r1} : NockEval a b (.val r1) → Pending n a c →
      Pending (n + 1) a (cell (atom 2) (cell b c))
  | op2_run {n a b c r1 r2} : NockEval a b (.val r1) → NockEval a c (.val r2) → Pending n r1 r2 →
      Pending (n + 1) a (cell (atom 2) (cell b c))
  -- 3, 4
  | op3 {n a b} : Pending n a b → Pending (n + 1) a (cell (atom 3) b)
  | op4 {n a b} : Pending n a b → Pending (n + 1) a (cell (atom 4) b)
  -- 5
  | op5_b {n a b c} : Pending n a b → Pending (n + 1) a (cell (atom 5) (cell b c))
  | op5_c {n a b c r1} : NockEval a b (.val r1) → Pending n a c →
      Pending (n + 1) a (cell (atom 5) (cell b c))
  -- 6
  | op6_b {n a b c d} : Pending n a b → Pending (n + 1) a (cell (atom 6) (cell b (cell c d)))
  | op6_then {n a b c d} : NockEval a b (.val (atom 0)) → Pending n a c →
      Pending (n + 1) a (cell (atom 6) (cell b (cell c d)))
  | op6_else {n a b c d} : NockEval a b (.val (atom 1)) → Pending n a d →
      Pending (n + 1) a (cell (atom 6) (cell b (cell c d)))
  -- 7
  | op7_b {n a b c} : Pending n a b → Pending (n + 1) a (cell (atom 7) (cell b c))
  | op7_c {n a b c r1} : NockEval a b (.val r1) → Pending n r1 c →
      Pending (n + 1) a (cell (atom 7) (cell b c))
  -- 8
  | op8_b {n a b c} : Pending n a b → Pending (n + 1) a (cell (atom 8) (cell b c))
  | op8_c {n a b c r1} : NockEval a b (.val r1) → Pending n (cell r1 a) c →
      Pending (n + 1) a (cell (atom 8) (cell b c))
  -- 9
  | op9_c {n a b c} : Pending n a c → Pending (n + 1) a (cell (atom 9) (cell b c))
  | op9_arm {n a b c core arm} : NockEval a c (.val core) → fasO b core = some arm →
      Pending n core arm → Pending (n + 1) a (cell (atom 9) (cell b c))
  -- 10
  | op10_d {n a b c d} : Pending n a d → Pending (n + 1) a (cell (atom 10) (cell (cell b c) d))
  | op10_c {n a b c d r2} : NockEval a d (.val r2) → Pending n a c →
      Pending (n + 1) a (cell (atom 10) (cell (cell b c) d))
  -- 11
  | op11_static {n a t c} : Pending n a c → Pending n a (cell (atom 11) (cell (atom t) c))
  | op11_dyn_c {n a t c d} : Pending n a c → Pending (n + 1) a (cell (atom 11) (cell (cell t c) d))
  | op11_dyn_d {n a t c d r1} : NockEval a c (.val r1) → Pending n a d →
      Pending (n + 1) a (cell (atom 11) (cell (cell t c) d))

/-- An atom in formula position is pending only at `0`. -/
theorem pending_atom {n : Nat} {s : Noun} {m : Nat} (h : Pending n s (atom m)) : n = 0 := by
  cases h; rfl

/-- The three possibilities for an operand (classical). -/
theorem outcome_cases (s b : Noun) :
    NoOut s b ∨ NockEval s b .exit ∨ ∃ r, NockEval s b (.val r) := by
  by_cases h : ∃ o, NockEval s b o
  · obtain ⟨o, ho⟩ := h
    cases o with
    | exit => exact .inr (.inl ho)
    | val r => exact .inr (.inr ⟨r, ho⟩)
  · exact .inl fun o ho => h ⟨o, ho⟩

/-- **A run with no outcome is pending at every `n`.** -/
theorem pending_of_noOut : ∀ (n : Nat) (f s : Noun), NoOut s f → Pending n s f
  | 0, _, _, _ => .zero
  | _ + 1, atom _, _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | n + 1, cell (cell b c) d, s, h => by
    rcases outcome_cases s (cell b c) with hb | hb | ⟨r1, hb⟩
    · exact .autocons_L (pending_of_noOut n _ s hb)
    · exact absurd (NockEval.autocons_crashL hb) (h _)
    · rcases outcome_cases s d with hd | hd | ⟨r2, hd⟩
      · exact .autocons_R hb (pending_of_noOut n d s hd)
      · exact absurd (NockEval.autocons_crashR hb hd) (h _)
      · exact absurd (NockEval.autocons hb hd) (h _)
  | _ + 1, cell (atom 0) fol, s, h => by
    cases hf : fasO fol s with
    | none => exact absurd (NockEval.op0_crash hf) (h _)
    | some r => exact absurd (NockEval.op0 hf) (h _)
  | _ + 1, cell (atom 1) _, _, h => absurd NockEval.op1 (h _)
  | n + 1, cell (atom 2) (cell b c), s, h => by
    rcases outcome_cases s b with hb | hb | ⟨r1, hb⟩
    · exact .op2_b (pending_of_noOut n b s hb)
    · exact absurd (NockEval.op2_crashL hb) (h _)
    · rcases outcome_cases s c with hc | hc | ⟨r2, hc⟩
      · exact .op2_c hb (pending_of_noOut n c s hc)
      · exact absurd (NockEval.op2_crashR hb hc) (h _)
      · exact .op2_run hb hc (pending_of_noOut n r2 r1 fun o ho => h o (NockEval.op2 hb hc ho))
  | _ + 1, cell (atom 2) (atom _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | n + 1, cell (atom 3) b, s, h => by
    rcases outcome_cases s b with hb | hb | ⟨r, hb⟩
    · exact .op3 (pending_of_noOut n b s hb)
    · exact absurd (NockEval.op3_crash hb) (h _)
    · exact absurd (NockEval.op3 hb) (h _)
  | n + 1, cell (atom 4) b, s, h => by
    rcases outcome_cases s b with hb | hb | ⟨r, hb⟩
    · exact .op4 (pending_of_noOut n b s hb)
    · exact absurd (NockEval.op4_crash hb) (h _)
    · cases hl : lusO r with
      | none => exact absurd (NockEval.op4_cell hb hl) (h _)
      | some v => exact absurd (NockEval.op4 hb hl) (h _)
  | n + 1, cell (atom 5) (cell b c), s, h => by
    rcases outcome_cases s b with hb | hb | ⟨r1, hb⟩
    · exact .op5_b (pending_of_noOut n b s hb)
    · exact absurd (NockEval.op5_crashL hb) (h _)
    · rcases outcome_cases s c with hc | hc | ⟨r2, hc⟩
      · exact .op5_c hb (pending_of_noOut n c s hc)
      · exact absurd (NockEval.op5_crashR hb hc) (h _)
      · exact absurd (NockEval.op5 hb hc) (h _)
  | _ + 1, cell (atom 5) (atom _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | n + 1, cell (atom 6) (cell b (cell c d)), s, h => by
    rcases outcome_cases s b with hb | hb | ⟨r, hb⟩
    · exact .op6_b (pending_of_noOut n b s hb)
    · exact absurd (NockEval.op6_crash hb) (h _)
    · by_cases h0 : r = atom 0
      · subst h0
        rcases outcome_cases s c with hc | hc | ⟨rc, hc⟩
        · exact .op6_then hb (pending_of_noOut n c s hc)
        · exact absurd (NockEval.op6_then hb hc) (h _)
        · exact absurd (NockEval.op6_then hb hc) (h _)
      · by_cases h1 : r = atom 1
        · subst h1
          rcases outcome_cases s d with hd | hd | ⟨rd, hd⟩
          · exact .op6_else hb (pending_of_noOut n d s hd)
          · exact absurd (NockEval.op6_else hb hd) (h _)
          · exact absurd (NockEval.op6_else hb hd) (h _)
        · exact absurd (NockEval.op6_nonloob hb h0 h1) (h _)
  | _ + 1, cell (atom 6) (atom _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | _ + 1, cell (atom 6) (cell _ (atom _)), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | n + 1, cell (atom 7) (cell b c), s, h => by
    rcases outcome_cases s b with hb | hb | ⟨r1, hb⟩
    · exact .op7_b (pending_of_noOut n b s hb)
    · exact absurd (NockEval.op7_crash hb) (h _)
    · exact .op7_c hb (pending_of_noOut n c r1 fun o ho => h o (NockEval.op7 hb ho))
  | _ + 1, cell (atom 7) (atom _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | n + 1, cell (atom 8) (cell b c), s, h => by
    rcases outcome_cases s b with hb | hb | ⟨r1, hb⟩
    · exact .op8_b (pending_of_noOut n b s hb)
    · exact absurd (NockEval.op8_crash hb) (h _)
    · exact .op8_c hb (pending_of_noOut n c (cell r1 s) fun o ho => h o (NockEval.op8 hb ho))
  | _ + 1, cell (atom 8) (atom _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | n + 1, cell (atom 9) (cell b c), s, h => by
    rcases outcome_cases s c with hc | hc | ⟨core, hc⟩
    · exact .op9_c (pending_of_noOut n c s hc)
    · exact absurd (NockEval.op9_crash hc) (h _)
    · cases hf : fasO b core with
      | none => exact absurd (NockEval.op9_badaxis hc hf) (h _)
      | some arm =>
        exact .op9_arm hc hf (pending_of_noOut n arm core fun o ho => h o (NockEval.op9 hc hf ho))
  | _ + 1, cell (atom 9) (atom _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | n + 1, cell (atom 10) (cell (cell b c) d), s, h => by
    rcases outcome_cases s d with hd | hd | ⟨r2, hd⟩
    · exact .op10_d (pending_of_noOut n d s hd)
    · exact absurd (NockEval.op10_crashTree hd) (h _)
    · rcases outcome_cases s c with hc | hc | ⟨r1, hc⟩
      · exact .op10_c hd (pending_of_noOut n c s hc)
      · exact absurd (NockEval.op10_crashPatch hd hc) (h _)
      · cases hx : haxO b r1 r2 with
        | none => exact absurd (NockEval.op10_badaxis hd hc hx) (h _)
        | some v => exact absurd (NockEval.op10 hd hc hx) (h _)
  | _ + 1, cell (atom 10) (atom _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | _ + 1, cell (atom 10) (cell (atom _) _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | n + 1, cell (atom 11) (cell (atom t) c), s, h =>
    .op11_static (pending_of_noOut (n + 1) c s fun o ho => h o (NockEval.op11_static ho))
  | n + 1, cell (atom 11) (cell (cell t c) d), s, h => by
    rcases outcome_cases s c with hc | hc | ⟨r1, hc⟩
    · exact .op11_dyn_c (pending_of_noOut n c s hc)
    · exact absurd (NockEval.op11_dyn_crash hc) (h _)
    · rcases outcome_cases s d with hd | hd | ⟨r2, hd⟩
      · exact .op11_dyn_d hc (pending_of_noOut n d s hd)
      · exact absurd (NockEval.op11_dynamic hc hd) (h _)
      · exact absurd (NockEval.op11_dynamic hc hd) (h _)
  | _ + 1, cell (atom 11) (atom _), _, h => absurd (NockEval.crash_malformed rfl) (h _)
  | _ + 1, cell (atom (_ + 12)) t, _, h => by
    cases t <;> exact absurd (NockEval.crash_malformed rfl) (h _)
termination_by n f => (n, sizeOf f)
decreasing_by all_goals simp_wf; all_goals omega

end Nock2Ski
