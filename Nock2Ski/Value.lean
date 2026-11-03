import Nock2Ski.Noun

open Term

/-!
# The value a term computes, read as a noun (M4f)

The probe circuit (lean-ski, `Ski/AirProbe.lean`) reads a term by applying
it to marker atoms constructor by constructor; what it certifies is a
**probe tree** (`Probe.V`), and `Nock2Ski/ProbeTree.lean` gives the tree of
a noun's encoding.  The theorem that joins the circuit to Nock has to be
read across two Lean environments: lean-ski's `Ski.ProbeTree` reaches
`Ski.Words`, whose root-level `Outcome` clashes with lean-nock's
(`Ski/Words.lean:157`, `Nock/Eval.lean:62`), so no module imports both
`Probe.DecV` and `NockEval`.  This module is the vocabulary both sides
share: it imports `Nock2Ski.Noun` (lean-nock's `Nock.Basic` and lean-ski's
`Ski.Compile`, which coexist) and nothing of either `Eval`.

- `EncS n e`: `e` has the **shape** of an encoding of `n`: an atom as
  `encNoun`, a cell as `Cell` of shapes of its halves or as `Form` of them
  with any code.  `Enc n e` (`Nock2Ski/Enc.lean`, which needs `Nock.Eval`
  for the code `nockToSki n`) implies it (`encS_of_enc`,
  `Nock2Ski/Probe.lean`).
- `ValueIs t p`: `t` has a weak head normal form `v`, `v` is not the crash,
  and every encoding-shaped term that `v` weakly reduces to encodes `p`.
  `Nock2Ski/ProbeTree.lean` proves it from the circuit's reading
  (`probe_value`, `probe_sound`); `Nock2Ski/Probe.lean` carries it to
  `NockEval s f (.val p)` (`probe_decodes_nock`).
-/

namespace Nock2Ski

/-- `e` has the shape of an encoding of `n`: an atom as `encNoun`, a cell
    as a `Cell` or a `Form` with any code. -/
inductive EncS : Noun → Term → Prop
  | atom (n : Nat) : EncS (.atom n) (encNoun (.atom n))
  | cell {h t : Noun} {eh et : Term} : EncS h eh → EncS t et → EncS (.cell h t) (cellT eh et)
  | form {h t : Noun} {eh et : Term} (k : Term) : EncS h eh → EncS t et →
      EncS (.cell h t) (formT eh et k)

/-- The code-free encoding has its noun's shape. -/
theorem encS_encNoun : ∀ n, EncS n (encNoun n)
  | .atom n => .atom n
  | .cell h t => .cell (encS_encNoun h) (encS_encNoun t)

/-- **The value of `t` is `p`**: `t` has a weak head normal form `v`, `v`
    does not weakly reduce to the crash `Err`, and every encoding-shaped
    term it weakly reduces to encodes `p`. -/
def ValueIs (t : Term) (p : Noun) : Prop :=
  ∃ v, Eval t v ∧ ¬ WSteps v errT ∧ ∀ q ep, EncS q ep → WSteps v ep → q = p

end Nock2Ski
