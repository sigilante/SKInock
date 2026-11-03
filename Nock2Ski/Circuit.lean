import Nock2Ski.ProbeTree
import Nock2Ski.Probe
import Ski.Circuit.ProbeRows
import Ski.Circuit.CompPred

open Nock
open Term

/-!
# The accepted proofs as Nock claims: lean-ski's circuits composed with the simulation

Until lean-nock's `namespace Nock` (its branch `namespace-nock`), lean-ski's
circuit modules could not be imported beside lean-nock: `Ski.Composed` and
`Ski.AirProbe` reach `Ski.Words`, whose root-level `Outcome` clashed with
lean-nock's, so the joins between lean-ski's export theorems and this
package's Nock readings were made through one shared constant per join
(`ValueIs` for the probe step, `Eval … K` for the predicate statements) and
read across two Lean environments.  This module imports both sides and
states each join as one theorem:

- **The probe step** (M4f, M4g).  `probe_proof_nock`: a proof Plonky3
  accepts against AIRs matching `Circuit.probeAirs t roots jets (planOf
  (nounV p) 0)` for the row's term `t = compiled f s`, with licensed roots
  and fitting numbers (what `ski-air probe-verify` checks through Lean
  before it verifies), is a proof of `*[s f] = p`:
  `Circuit.probeExport_sound_tree` (lean-ski branch `probe-plan-file`,
  generic in the tree) gives `DecV t.toO (nounV p)`, `probe_value`
  (`Nock2Ski/ProbeTree.lean`) makes it `ValueIs t p`, and
  `probe_decodes_nock` (`Nock2Ski/Probe.lean`) reads Nock's value off it.
  `probe_proof_nock_shared` is the same of `share (compiled f s)`;
  `probe_table_nock` the same of a witness table `Air.checkPA` accepts
  (`lake exe nockprobe check`), through `probe_check`.
- **The hidden-subject statements** (M4c, M4d, M4e).  `pred_proof_nock`: a
  proof accepted against AIRs matching `Circuit.predAirs (nockPredV f k)
  (encNoun p) k W` shows an atom `n < 2^k` with `*[n f] = p`:
  `Circuit.predExport_sound` concludes `Eval (V ⬝ x ⬝ boolsT bs) K` for the
  proof's `k` memory bits `bs`, and `nock_pred_sound_nock`
  (`Nock2Ski/Converse.lean`) is the Nock reading of that acceptance.
  `predS_proof_nock` and `pred2_proof_nock` are the same for a skeleton
  and for `[?k ?k]`.  `Nock2Ski/Pred.lean`'s `boolsT` was a copy of
  lean-ski's `CompM.boolsT`; `boolsT_eq` is the equality, so the
  composition is one `obtain` and a rewrite.

The theorems take `[Kit]` as lean-ski's probe theorems do; they are not
used.  What remains read by inspection is the statement's text:
`Nock2Ski/PredText.lean` renders `public.txt` with copies of lean-ski's
`ComposedText` definitions, and ski-air checks the bytes against lean-ski's
`lake exe composed statement` before it proves or verifies.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- The probe step: an accepted probe proof is `*[s f] = p`
-- ---------------------------------------------------------------------------

/-- **An accepted probe proof of the `plain` row is a proof of `*[s f] =
    p`**, with `p` read from the public plan `planOf (nounV p) 0`. -/
theorem probe_proof_nock [Kit] {s f p : Noun} {roots : List (Nat × Nat)} {jets : List Air.Jet}
    (hroots : Air.rootsOKB (Mach.load (compiled f s)).heap roots jets = true)
    (hjfit : jets.all Circuit.jetFitB = true)
    (hfit : Circuit.planFitB (Air.planOf (nounV p) 0) = true)
    {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs (Circuit.probeAirs (compiled f s) roots jets (Air.planOf (nounV p) 0)) = true)
    (h : Circuit.AcceptedP Rs ts) : NockEval s f (.val p) :=
  probe_decodes_nock (probe_value (Circuit.probeExport_sound_tree hroots hjfit hfit hs h))

/-- The same of the `shared` row, `share (compiled f s)`. -/
theorem probe_proof_nock_shared [Kit] {s f p : Noun} {roots : List (Nat × Nat)} {jets : List Air.Jet}
    (hroots : Air.rootsOKB (Mach.load (share (compiled f s))).heap roots jets = true)
    (hjfit : jets.all Circuit.jetFitB = true)
    (hfit : Circuit.planFitB (Air.planOf (nounV p) 0) = true)
    {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs (Circuit.probeAirs (share (compiled f s)) roots jets (Air.planOf (nounV p) 0)) = true)
    (h : Circuit.AcceptedP Rs ts) : NockEval s f (.val p) :=
  probe_decodes_nock_shared (probe_value (Circuit.probeExport_sound_tree hroots hjfit hfit hs h))

/-- **An accepted probe table is `*[s f] = p`**: `Air.checkPA` (`lake exe
    nockprobe check`) accepting the table for `nounPlan p` on the row's
    term, through `probe_check`. -/
theorem probe_table_nock [Kit] {A : Array Cell} {s f p : Noun} {roots : List (Nat × Nat)}
    {jets : List Air.Jet} {starts : Array Nat} {flds : Array (List Nat)} {R : Array Air.Row}
    (h : Air.checkPA A (compiled f s) roots jets (nounPlan p) starts flds R = true) :
    NockEval s f (.val p) :=
  probe_decodes_nock (probe_check h)

theorem probe_table_nock_shared [Kit] {A : Array Cell} {s f p : Noun} {roots : List (Nat × Nat)}
    {jets : List Air.Jet} {starts : Array Nat} {flds : Array (List Nat)} {R : Array Air.Row}
    (h : Air.checkPA A (share (compiled f s)) roots jets (nounPlan p) starts flds R = true) :
    NockEval s f (.val p) :=
  probe_decodes_nock_shared (probe_check h)

-- ---------------------------------------------------------------------------
-- The hidden-subject statements: an accepted predicate proof is `*[n f] = p`
-- ---------------------------------------------------------------------------

/-- `Nock2Ski/Pred.lean`'s `boolsT` is lean-ski's `CompM.boolsT`. -/
theorem boolsT_eq : ∀ bs, boolsT bs = CompM.boolsT bs
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: r => by
    simp only [boolsT, CompM.boolsT]
    rw [boolsT_eq (_ :: r)]

/-- **An accepted proof of the predicate statement `nockPredV f k` on the
    product `p` shows an atom `n < 2^k` with `*[n f] = p`.** -/
theorem pred_proof_nock {f p : Noun} {k W : Nat} (hk : 0 < k)
    {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs (Circuit.predAirs (nockPredV f k) (encNoun p) k W) = true)
    (h : Circuit.AcceptedP Rs ts) : ∃ n, n < 2 ^ k ∧ NockEval (.atom n) f (.val p) := by
  obtain ⟨_, _, _, _, _, -, hl, hK⟩ := Circuit.predExport_sound hk hs h
  rw [← boolsT_eq] at hK
  exact nock_pred_sound_nock hk hl hK

/-- The same for a skeleton `sk`: the subject is the skeleton filled with
    the proof's bits. -/
theorem predS_proof_nock {f p : Noun} {sk : Skel} {W : Nat} (hok : sk.ok = true) (hw : 0 < sk.width)
    {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs (Circuit.predAirs (nockPredS f sk) (encNoun p) sk.width W) = true)
    (h : Circuit.AcceptedP Rs ts) : ∃ bs : List Bool, bs.length = sk.width ∧ NockEval (sk.fill bs) f (.val p) := by
  obtain ⟨_, _, _, _, _, -, hl, hK⟩ := Circuit.predExport_sound hw hs h
  rw [← boolsT_eq] at hK
  exact ⟨_, hl, nock_predS_sound_nock hok hl hK⟩

/-- The same for `[?k ?k]`: atoms `a, b < 2^k` with `*[[a b] f] = p`. -/
theorem pred2_proof_nock {f p : Noun} {k W : Nat} (hk : 0 < k)
    {Rs : List Circuit.AirD} {ts : List Circuit.Table}
    (hs : Circuit.sameAirsB Rs (Circuit.predAirs (nockPred2V f k) (encNoun p) (2 * k) W) = true)
    (h : Circuit.AcceptedP Rs ts) :
    ∃ a b, a < 2 ^ k ∧ b < 2 ^ k ∧ NockEval (.cell (.atom a) (.atom b)) f (.val p) := by
  obtain ⟨_, _, _, _, _, -, hl, hK⟩ := Circuit.predExport_sound (by omega) hs h
  rw [← boolsT_eq] at hK
  exact nock_pred2_sound_nock hk hl hK

end Nock2Ski
