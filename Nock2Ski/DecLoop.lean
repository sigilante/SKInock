import Nock2Ski.DecBridge
import Nock.Composition

open Nock
open Term

/-!
# A Λ loop around the word `dec`

`decLoop = while (top ≠ 0) dec`, written in lean-nock's term algebra on a
stack `[n [0 r]]` (the `0` below the counter is the constant the test
compares against, since Λ has no literal push):

- the test `over over eq ifte(over inc, over)`: `over over` copies the `0`
  and the counter to the top, `eq` leaves `0` when they are equal and `1`
  when not, and the branch turns that into `while`'s flag, `1` (stop) on
  `n = 0` and `0` (go on) otherwise, over the stack unchanged;
- the body `dec`.

`decLoopF = NT decLoop` is its Nock formula (lean-nock's `Λ_N`), and
`nockToSki decLoopF` its SKI term.  **`decLoop_nock`**: `*[[n [0 r]]
decLoopF] = [0 [0 r]]` for every `n` and `r`, from lean-nock's
`composition_term` and a `CEval` derivation by induction on `n` (the `dec`
leaf is `cw .dec`, Table C's row); **`decLoop_ski`**: the SKI term on the
encoded stack reduces to the encoding of `[0 [0 r]]` (`embed_value`, the
product code-free, so the encoding is `encNoun`'s up to `Enc`).

The loop runs the word `n` times and each `dec` of `k` runs lean-nock's
count-up loop `k` times, so the unjetted cost is quadratic in `n`.  lean-ski's
`dec` jet cannot stand in for the word here: in the compiled loop the word's
argument is never an `encNn` laid out in memory (it is the environment's
unevaluated projection, and a Scott cell's fields come out of elimination
as thunks), so the jet's row does not fire (`bench/NockDecLoop.lean probe`).
-/

namespace Nock2Ski

/-- The test: flag `1` on a zero counter, `0` otherwise, over the stack. -/
def decTest : Nock.Term :=
  .seq .over (.seq .over (.seq .eq (.ifte (.seq .over (.seq .inc .nil)) (.seq .over .nil) .nil)))

/-- **`while (top ≠ 0) dec`**. -/
def decLoop : Nock.Term := .while decTest (.seq .dec .nil) .nil

/-- Its Nock formula. -/
def decLoopF : Noun := NT decLoop

theorem decTest_zero (r : Noun) :
    CEval decTest (.cell (.atom 0) (.cell (.atom 0) r))
      (.val (.cell (.atom 1) (.cell (.atom 0) (.cell (.atom 0) r)))) := by
  refine CEval.seq rfl (CEval.seq rfl (CEval.seq rfl ?_))
  rw [tisN_refl]
  exact CEval.ifte_then (CEval.seq rfl (CEval.seq rfl CEval.nil)) CEval.nil

theorem decTest_succ (n : Nat) (r : Noun) :
    CEval decTest (.cell (.atom (n + 1)) (.cell (.atom 0) r))
      (.val (.cell (.atom 0) (.cell (.atom (n + 1)) (.cell (.atom 0) r)))) := by
  refine CEval.seq rfl (CEval.seq rfl (CEval.seq rfl ?_))
  rw [tisN_neq _ _ (by intro h; injection h; omega)]
  exact CEval.ifte_else (CEval.seq rfl CEval.nil) CEval.nil

theorem decLoop_ceval (r : Noun) : ∀ n : Nat,
    CEval decLoop (.cell (.atom n) (.cell (.atom 0) r)) (.val (.cell (.atom 0) (.cell (.atom 0) r)))
  | 0 => CEval.while_exit (decTest_zero r) CEval.nil
  | n + 1 => CEval.while_step (decTest_succ n r) (CEval.seq rfl CEval.nil) (decLoop_ceval r n)

/-- **The loop's Nock outcome**: `*[[n [0 r]] decLoopF] = [0 [0 r]]`. -/
theorem decLoop_nock (n : Nat) (r : Noun) :
    NockEval (.cell (.atom n) (.cell (.atom 0) r)) decLoopF (.val (.cell (.atom 0) (.cell (.atom 0) r))) :=
  (composition_term decLoop _ _).2 (decLoop_ceval r n)

/-- **The SKI term's outcome**: on the encoded stack, an encoding of
    `[0 [0 r]]`. -/
theorem decLoop_ski (n : Nat) (r : Noun) :
    ∃ e, Enc (.cell (.atom 0) (.cell (.atom 0) r)) e ∧
      WSteps (nockToSki decLoopF ⬝ encNoun (.cell (.atom n) (.cell (.atom 0) r))) e :=
  embed_value_encNoun (decLoop_nock n r)

end Nock2Ski
