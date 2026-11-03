import Nock.Eval
import Ski.Weak

open Nock

/-!
# Nock2Ski: the join

Milestone M0 of `PLAN.md`: one module that imports `Nock.Eval` (lean-nock) and
`Ski.Weak` (lean-ski) and type-checks against both.  The theorem below is
deliberately trivial; its job is to prove that one definition from each
library is in scope and that `lake build` closes.
-/

namespace Nock2Ski

/-- `Noun.atom 0` is not a cell: Nock's `?` returns `1` on it.  `Term.S` is not
`Term.K`.  One definition from each library. -/
theorem m0_join : wut (Noun.atom 0) = Noun.atom 1 ∧ Term.S ≠ Term.K :=
  ⟨rfl, Term.noConfusion⟩

end Nock2Ski
