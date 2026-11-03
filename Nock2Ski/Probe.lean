import Nock2Ski.Converse
import Nock2Ski.Value

open Term

/-!
# The public product as a public value of the proof (M4f)

The released rows (`release/nock/corpus.txt`) prove that `compiled f s` (or
`share (compiled f s)`) evaluates to a weak head normal form `v`, and
`embed_outcome` (`Nock2Ski/Converse.lean`) says `v` is an encoding of
Nock's product or `Err` for its crash, a Lean fact about `v`, which the
proof does not name.  lean-ski's probe circuit (`Ski/AirProbe.lean`) binds
an output: a table with probe segments, accepted for the plan of a probe
tree, proves that the term **reads** as that tree (`Air.air_probe_sound`),
and `Nock2Ski/ProbeTree.lean` gives the tree `nounV p` of our encoding of a
noun `p` and proves `probe_value`: a term that reads as `nounV p` has the
value `p` (`ValueIs t p`, `Nock2Ski/Value.lean`): it converges, not to
`Err`, and every encoding-shaped term its weak head normal form reaches
encodes `p`.

This module carries `ValueIs` to Nock:

- `probe_decodes_nock : ValueIs (compiled f s) p → NockEval s f (.val p)`,
  and `probe_decodes_nock_shared` for `share (compiled f s)`: from
  `embed_outcome`, since the final state is an encoding of Nock's value or
  `Err`, and `ValueIs` rules out `Err` and names the value.
- `probe_complete_nock : NockEval s f (.val (.atom n)) → WSteps (compiled
  f s) (encNoun (.atom n))`, the hypothesis of `ProbeTree.lean`'s
  `probe_complete`, so the prover can make the table for an atom product
  (an atom's encoding is `encNoun`'s, `Enc.atom_inv`; a cell product's
  term may be a `Form`, which no probe tree reads, see `ProbeTree.lean`).

**The join is read across two Lean environments**, as M4c's (`README.md`,
"Proofs"): `Ski.ProbeTree` reaches `Ski.Words`, whose root-level `Outcome`
(`Ski/Words.lean:157`) clashes with lean-nock's (`Nock/Eval.lean:62`), so
`Nock2Ski/ProbeTree.lean` (lean-ski's `DecV`, `AcceptsP`, `checkPA`) and
this module (`NockEval`) cannot be imported together.  They meet in
`Nock2Ski/Value.lean`, which both import: `ValueIs` is one constant, the
conclusion of `probe_sound`/`probe_check` there and the hypothesis of
`probe_decodes_nock` here; `encNoun` and `WSteps` likewise for
completeness.  Nothing is copied.

So an accepted probe table for `nounPlan p` on a row's term is a proof of
`NockEval s f (.val p)` with `p` a public input of the proof (its plan),
where the base rows name `p` only through Lean's `embed_outcome`.
-/

namespace Nock2Ski

/-- An encoding has an encoding's shape (its code is `nockToSki`). -/
theorem encS_of_enc : ∀ {n : Noun} {e : Term}, Enc n e → EncS n e
  | _, _, .atom n => .atom n
  | _, _, .cell hh ht => .cell (encS_of_enc hh) (encS_of_enc ht)
  | _, _, .form hh ht => .form _ (encS_of_enc hh) (encS_of_enc ht)

/-- **A read value is Nock's**: if the value of `nockToSki f ⬝ es` is `p`,
    Nock evaluates `f` on `s` to `p`. -/
theorem nock_of_valueIs {s f p : Noun} {es : Term} (hes : Enc s es)
    (h : ValueIs (nockToSki f ⬝ es) p) : NockEval s f (.val p) := by
  obtain ⟨v, hv, hne, hval⟩ := h
  rcases embed_outcome hes hv with ⟨q, ep, hq, hep, hw⟩ | ⟨_, herr⟩
  · rw [← hval q ep (encS_of_enc hep) hw]
    exact hq
  · exact absurd herr hne

/-- **`probe_decodes_nock`**: the value of the `plain` row's term is Nock's
    product.  `ValueIs (compiled f s) p` is what `ProbeTree.lean`'s
    `probe_sound` (`Air.air_probe_sound`) and `probe_check` (`Air.checkPA`)
    conclude of an accepted probe table for `nounPlan p`. -/
theorem probe_decodes_nock {s f p : Noun} (h : ValueIs (compiled f s) p) : NockEval s f (.val p) :=
  nock_of_valueIs (enc_encLit s) h

/-- The same of the `shared` row's term: `share (compiled f s)` weakly
    reduces to `compiled f s` (`share_red`), whose weak head normal form the
    shared term's reaches (`eval_wsteps`), so the value is the same. -/
theorem probe_decodes_nock_shared {s f p : Noun} (h : ValueIs (share (compiled f s)) p) :
    NockEval s f (.val p) := by
  obtain ⟨v, hv, hne, hval⟩ := h
  obtain ⟨N, hN⟩ := hlen_of_eval hv
  obtain ⟨M, _, hM⟩ := hlen_wsteps (share_red _) hN
  obtain ⟨v', hv'⟩ := hM.eval
  have hvv' : WSteps v v' := eval_wsteps hv'.2 ((share_red _).trans hv'.1.weak) hv
  exact probe_decodes_nock ⟨v', hv', fun herr => hne (hvv'.trans herr),
    fun q ep hq hw => hval q ep hq (hvv'.trans hw)⟩

/-- **Completeness for an atom product**: the row's term weakly reduces to
    `encNoun (.atom n)`, so it reads as `nounV (.atom n)` (`ProbeTree.lean`,
    `probe_complete`) and the prover can make the table. -/
theorem probe_complete_nock {s f : Noun} {n : Nat} (h : NockEval s f (.val (.atom n))) :
    WSteps (compiled f s) (encNoun (.atom n)) := by
  obtain ⟨ep, hep, hw⟩ := compiled_value h
  rw [hep.atom_inv] at hw
  exact hw

theorem probe_complete_nock_shared {s f : Noun} {n : Nat} (h : NockEval s f (.val (.atom n))) :
    WSteps (share (compiled f s)) (encNoun (.atom n)) :=
  (share_red _).trans (probe_complete_nock h)

/-- A cell product whose term is code-free reads too: `Enc p ep` with
    `ep = encNoun p` is the case where no `Form` was produced. -/
theorem probe_complete_nock_cell {s f p : Noun} (h : NockEval s f (.val p))
    (hc : ∀ ep, Enc p ep → WSteps (compiled f s) ep → ep = encNoun p) :
    WSteps (compiled f s) (encNoun p) := by
  obtain ⟨ep, hep, hw⟩ := compiled_value h
  rw [hc ep hep hw] at hw
  exact hw

end Nock2Ski
