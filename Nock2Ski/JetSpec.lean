import Nock.Eval
import Nock.Notation

open Nock
open Noun

/-!
# The vocabulary of jet transport (M5)

lean-nock states a Λ word's leaf contract as `leaf_correct w : NockEval S
(phi w) (cw w S)` for every subject `S` (`Nock/Comp.lean`): the word's Nock
formula `phi w` evaluates to exactly what the C model `cw w` returns, a
value or a crash, on every noun.  lean-ski licenses a data jet by a
`Contract` and `Implements` (`Ski/DataJet.lean`).

This module is the vocabulary of the transport, as `Nock2Ski/Value.lean`
is for the probe step: it imports lean-nock's `Nock.Eval` and nothing of
lean-ski.  (Until lean-nock's `namespace Nock`, its branch
`namespace-nock`, `Nock.Comp` reached `Nock.Fuel`, whose root-level
`Diverges` clashed with `Ski.Basic`'s, so no module that saw `Word`, `phi`
or `cw` could see `Term`, and this module was where the two sides met
through one constant.  Now `Nock2Ski/JetTransport.lean` imports
`Nock2Ski/JetWord.lean` directly and the instances are unconditional.)

- `Leaf f c`: the formula `f` evaluates on every subject to the total model
  `c`'s outcome, lean-nock's leaf-correctness shape.  `Nock2Ski/JetWord.lean`
  proves it for the words from `leaf_correct`; `Nock2Ski/JetTransport.lean`
  takes it as the hypothesis of `jet_transport` and composes the two in
  `dec_transport`, `add_transport`.
- `decF`, `addF`: the Nock formulas of the Λ words `dec` and `add`, `phi .dec`
  and `phi .add` written out (lean-nock's Table C: the guarded count-up
  decrement lifted to a stack word, and the guarded inc-loop over a pair);
  `decC`, `addC`: their C models, `cw .dec` and `cw .add` clause for clause.
  `JetWord.lean` proves each equal to lean-nock's (`decF_eq`, `decC_eq`, …),
  by `rfl` and by cases.

A total model has two outcomes, value and crash; divergence is the absence
of a `NockEval` derivation and has no place in `c`.  `Leaf f c` therefore
says in particular that `f` has an outcome on every subject, which is
lean-nock's `word_crash_total`, the guards Λ emits.
-/

namespace Nock2Ski

/-- **Leaf correctness** of a formula `f` against a total model `c`: on
    every subject, Nock derives exactly `c S`. -/
def Leaf (f : Noun) (c : Noun → Outcome) : Prop := ∀ S, NockEval S f (c S)

/-- `phi .dec`: `[[7 [0 2] <guarded-dec>] 0 3]`, the guarded count-up
    decrement on the top of the stack, consed back onto the rest. -/
def decF : Noun :=
  n! "[[7 [0 2] 6 [3 0 1] [0 0] 6 [5 [1 0] 0 1] [0 0] 8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1] 0 3]"

/-- `phi .add`: `[[7 [[0 6] 0 2] <guarded-inc-loop>] 0 7]`, on a stack
    `[b [a r]]`. -/
def addF : Noun :=
  n! "[[7 [[0 6] 0 2] 6 [3 0 2] [0 0] 6 [3 0 3] [0 0] 8 [1 0] 8 [1 6 [5 [0 6] 0 15] [0 14] 9 2 [0 2] [4 0 6] [4 0 14] 0 15] 9 2 0 1] 0 7]"

/-- `cw .dec`: Table C's `dec` row, every clause. -/
def decC : Noun → Outcome
  | atom _ => .exit                                  -- depth < 1
  | cell (atom 0) _ => .exit                         -- underflow
  | cell (cell _ _) _ => .exit                       -- cell argument
  | cell (atom (n + 1)) r => .val (cell (atom n) r)

/-- `cw .add`: Table C's `add` row, on `[b [a r]]`. -/
def addC : Noun → Outcome
  | atom _ => .exit                                   -- depth < 2
  | cell _ (atom _) => .exit                          -- depth < 2
  | cell (cell _ _) (cell _ _) => .exit               -- b is a cell
  | cell (atom _) (cell (cell _ _) _) => .exit        -- a is a cell
  | cell (atom b) (cell (atom a) r) => .val (cell (atom (a + b)) r)

end Nock2Ski
