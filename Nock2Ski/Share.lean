import Nock2Ski.Embed
import Std.Data.HashMap

open Nock
open Term

/-!
# Sharing in the term: repeated subterms bound once

Milestone M4b of `PLAN.md`.  `encLit` gives a battery's nested formula
literals their code once per nesting level, so a term's tree is
exponentially larger than its DAG (Hoon's `++dec` is 2,154,393 cells as a
tree, 2.7% over the 2^21 cells of the circuit's memory table, and about
6,000 nodes as a DAG).  ski-air loads a term cell by cell with no sharing
(`build` in lean-ski's `bench/plonky3/src/main.rs`), and Python's
hash-consing (`compile.py`) shares the DAG only in Avon's `dag` form, not
in the prefix text.  The fix is sharing *in the term*: a subterm that
occurs more than once is bound with a λ, so it appears once syntactically
and the heap shares it after the β.

## The construction

`plan minSize t` hash-conses `t` into a DAG and picks every node of at
least `minSize` cells with two or more parent edges (the nodes the tree
would write more than once).  Those are the bound subterms `L₁ … Lₙ`,
numbered smallest first, so each `Lⱼ` may contain earlier `Lᵢ` and no
later one; its body `Lⱼ'` is `Lⱼ` with its maximal bound subterms replaced
by their variables, and `C` is `t` with the same replacement.  The term is
the let chain

    share t = (λx₁. (λx₂. … (λxₙ. C) Lₙ') …) L₂') L₁'

with each λ bracket abstraction (`absO`, lean-ski's linear-time `abs`),
`chain`.  Smaller subterms are bound outermost so that the nested sharing
inside a bound subterm is itself shared: the DAG is written once.

## The theorem

`share_red : WSteps (share t) t`.  Each β is lean-ski's
`abs_beta_close`, and after all `n` the result is `C.close σ` with `σ xⱼ =
Lⱼ`, which is `t` itself.  `shareWith` checks that equation (`C.close σ =
t`, decidable) before it returns the chain and returns `t` unchanged
otherwise, so the theorem holds of the plan by construction and the
hash-consing is not part of the trusted path; `nockstatement` prints the
cell counts, so a plan that failed the check would be visible as an
unshared row.  The corollaries `shared_value` and `shared_crash` are
`compiled_value`/`compiled_crash` behind `WSteps.trans share_red`.

## Encodings are weak head normal forms

`enc_whnf : Enc p ep → Whnf ep` (every constructor is `S ⬝ _ ⬝ _` or
`K ⬝ _`), the lemma that joins the circuit's statement to the embedding:
lean-ski's `Circuit.export_sound` gives `Eval t v` for the public term `t`
and the proof's final state `v`; `eval_back` with `enc_whnf` and
`Eval.deterministic` then give `WSteps v ep` (`eval_enc`), so the final
state of an accepted proof of the row `share (compiled f s)` weakly reduces
to an encoding of Nock's product (`shared_value_eval`), or to `errT` on a
crash (`shared_crash_eval`); `compiled_value_eval` and
`compiled_crash_eval` are the same for the unshared row.
-/

namespace Nock2Ski

-- ---------------------------------------------------------------------------
-- The let chain and its β
-- ---------------------------------------------------------------------------

/-- The closing environment of a closed chain: every variable is bound. -/
def γK : Nat → Term := fun _ => K

/-- Bindings, outermost first: a variable and its body over the earlier
    variables. -/
abbrev Binds := List (Nat × OTerm)

/-- `(λx₁. (λx₂. … C) L₂') L₁'`, each λ by bracket abstraction. -/
def chain : Binds → OTerm → OTerm
  | [], C => C
  | (x, L) :: bs, C => (absO x (chain bs C)).1 ⬝ₒ L

/-- The environment after the bindings: `xⱼ ↦ Lⱼ'` closed under the
    earlier ones. -/
def extend (γ : Nat → Term) : Binds → Nat → Term
  | [] => γ
  | (x, L) :: bs => extend (updC γ x (L.close γ)) bs

/-- **β along the chain**: one `abs_beta_close` per binding. -/
theorem chain_red : ∀ (bs : Binds) (C : OTerm) (γ : Nat → Term),
    WSteps ((chain bs C).close γ) (C.close (extend γ bs))
  | [], _, _ => .refl _
  | (x, L) :: bs, C, γ => by
    show WSteps ((absO x (chain bs C)).1.close γ ⬝ L.close γ) _
    rw [absO_eq]
    exact (abs_beta_close x (chain bs C) γ (L.close γ)).trans (chain_red bs C _)

/-- The chain of a plan, when the plan's substitution gives `t` back;
    `t` itself otherwise. -/
def shareWith (bs : Binds) (C : OTerm) (t : Term) : Term :=
  if C.close (extend γK bs) = t then (chain bs C).close γK else t

theorem shareWith_red (bs : Binds) (C : OTerm) (t : Term) : WSteps (shareWith bs C t) t := by
  unfold shareWith
  split
  · next h => rw [← h]; exact chain_red bs C γK
  · exact .refl t

-- ---------------------------------------------------------------------------
-- The plan: hash-consing
-- ---------------------------------------------------------------------------

/-- A node of the hash-consed DAG; children are earlier indices. -/
inductive DNode
  | S | K | I
  | app (f a : Nat)
  deriving BEq, Hashable, Inhabited, Repr

/-- The DAG of a term: every distinct subterm once, children before
    parents, the root last. -/
structure Dag where
  nodes : Array DNode
  root : Nat

/-- Hash-cons a term, iteratively (the terms are deep). -/
def Dag.ofTerm (t : Term) : Dag := Id.run do
  let mut nodes : Array DNode := #[]
  let mut table : Std.HashMap DNode Nat := {}
  let mut results : Array Nat := #[]
  let mut stack : List (Term × Bool) := [(t, false)]
  let intern := fun (nodes : Array DNode) (table : Std.HashMap DNode Nat) (n : DNode) =>
    match table[n]? with
    | some i => (nodes, table, i)
    | none => (nodes.push n, table.insert n nodes.size, nodes.size)
  repeat
    match stack with
    | [] => break
    | (u, done) :: rest =>
      stack := rest
      match u with
      | .app f a =>
        if done then
          let ia := results.back!
          results := results.pop
          let «if» := results.back!
          results := results.pop
          let (ns, tb, i) := intern nodes table (.app «if» ia)
          nodes := ns; table := tb; results := results.push i
        else
          stack := (f, false) :: (a, false) :: (u, true) :: rest
      | .S => let (ns, tb, i) := intern nodes table .S; nodes := ns; table := tb; results := results.push i
      | .K => let (ns, tb, i) := intern nodes table .K; nodes := ns; table := tb; results := results.push i
      | .I => let (ns, tb, i) := intern nodes table .I; nodes := ns; table := tb; results := results.push i
  return ⟨nodes, results.back!⟩

/-- The tree size of each node. -/
def Dag.sizes (d : Dag) : Array Nat := Id.run do
  let mut sz : Array Nat := Array.replicate d.nodes.size 0
  for i in [0:d.nodes.size] do
    match d.nodes[i]! with
    | .app f a => sz := sz.set! i (1 + sz[f]! + sz[a]!)
    | _ => sz := sz.set! i 1
  return sz

/-- The number of parent edges of each node, with multiplicity: the
    number of times the tree writes it, per copy of its parents. -/
def Dag.indegs (d : Dag) : Array Nat := Id.run do
  let mut deg : Array Nat := Array.replicate d.nodes.size 0
  for i in [0:d.nodes.size] do
    match d.nodes[i]! with
    | .app f a => deg := (deg.set! f (deg[f]! + 1)); deg := deg.set! a (deg[a]! + 1)
    | _ => pure ()
  return deg

/-- The plan: bind every node of at least `minSize` cells with two or more
    parent edges, smallest first; the body of each is its node with its
    maximal bound subterms as variables, and `C` is the root's. -/
def plan (minSize : Nat) (t : Term) : Binds × OTerm := Id.run do
  let d := Dag.ofTerm t
  let sz := d.sizes
  let deg := d.indegs
  let mut ot : Array OTerm := Array.replicate d.nodes.size .S
  let mut bs : Array (Nat × OTerm) := #[]
  for i in [0:d.nodes.size] do
    match d.nodes[i]! with
    | .S => ot := ot.set! i .S
    | .K => ot := ot.set! i .K
    | .I => ot := ot.set! i .I
    | .app f a =>
      let body := ot[f]! ⬝ₒ ot[a]!
      if i != d.root && deg[i]! ≥ 2 && sz[i]! ≥ minSize then
        bs := bs.push (bs.size, body)
        ot := ot.set! i (.var bs.size.pred)
      else
        ot := ot.set! i body
  return (bs.toList, ot[d.root]!)

/-- `share` with the size threshold given. -/
def shareT (minSize : Nat) (t : Term) : Term :=
  let p := plan minSize t
  shareWith p.1 p.2 t

/-- The threshold.  A binding costs cells (the `S`/`K` spine that
    delivers the variable to its uses, a `K` per body it is in scope over
    and does not reach) and contractions at run time (those same `S`/`K`
    steps, once per copy of the thunk that is forced), so subterms below
    it are written out.  `nockstatement --cells` is the sweep; on Hoon's
    `++dec` the tree is 2,154,393 cells and 28,324 contractions, and
    sharing gives 368,077 cells and 316,721 contractions at 32, 58,921 and
    35,433 at 512, 60,217 and 33,043 at 1024, 80,907 and 30,632 at 4096,
    1,474,005 and 28,413 at 131,072; the count-up `dec` (139,919 cells,
    12,004 contractions) gives 32,549 and 12,962 at 1024. -/
def shareMin : Nat := 1024

/-- **Sharing**: the let chain of `t`'s repeated subterms. -/
def share (t : Term) : Term := shareT shareMin t

theorem shareT_red (minSize : Nat) (t : Term) : WSteps (shareT minSize t) t :=
  shareWith_red _ _ t

/-- **`share_red`**: the shared term weakly reduces to the term, by `n` βs. -/
theorem share_red (t : Term) : WSteps (share t) t := shareT_red _ t

/-- `plan` with terms kept literal: a node equal to a term of `keep` gets
    its literal code as its body (its own repeated subterms are not replaced
    by variables inside it), so the shared term contains each kept term
    verbatim.  Bound subterms inside it may still be bound for their uses
    elsewhere.  A runtime that binds pinned terms at load (Avon's
    `av_pin_bind`) then finds them in the shared program.  With `keep = []`
    this is `plan`. -/
def planKeep (minSize : Nat) (keep : List Term) (t : Term) : Binds × OTerm := Id.run do
  let d := Dag.ofTerm t
  let sz := d.sizes
  let deg := d.indegs
  let keepO := keep.map fun k => (treeSizeK k, k.toO)
  let mut ot : Array OTerm := Array.replicate d.nodes.size .S
  let mut lit : Array OTerm := Array.replicate d.nodes.size .S
  let mut bs : Array (Nat × OTerm) := #[]
  for i in [0:d.nodes.size] do
    match d.nodes[i]! with
    | .S => ot := ot.set! i .S; lit := lit.set! i .S
    | .K => ot := ot.set! i .K; lit := lit.set! i .K
    | .I => ot := ot.set! i .I; lit := lit.set! i .I
    | .app f a =>
      let l := lit[f]! ⬝ₒ lit[a]!
      lit := lit.set! i l
      let kept := keepO.any fun (n, k) => n == sz[i]! && k == l
      let body := if kept then l else ot[f]! ⬝ₒ ot[a]!
      if i != d.root && deg[i]! ≥ 2 && sz[i]! ≥ minSize then
        bs := bs.push (bs.size, body)
        ot := ot.set! i (.var bs.size.pred)
      else
        ot := ot.set! i body
  return (bs.toList, ot[d.root]!)
where
  /-- The tree size as `Dag.sizes` counts it: every node, leaves and
      applications. -/
  treeSizeK : Term → Nat
    | .app f a => 1 + treeSizeK f + treeSizeK a
    | _ => 1

/-- **Sharing that keeps the given terms literal** (`planKeep`). -/
def shareKeep (keep : List Term) (t : Term) : Term :=
  let p := planKeep shareMin keep t
  shareWith p.1 p.2 t

/-- **`shareKeep_red`**: as `share_red`, by `shareWith`'s check. -/
theorem shareKeep_red (keep : List Term) (t : Term) : WSteps (shareKeep keep t) t :=
  shareWith_red _ _ t

/-- The number of bindings a plan makes. -/
def shareCount (minSize : Nat) (t : Term) : Nat := (plan minSize t).1.length

-- ---------------------------------------------------------------------------
-- The shared program
-- ---------------------------------------------------------------------------

/-- **`shared_value`**: the shared program reduces to an encoding of the
    product. -/
theorem shared_value {s f p : Noun} (h : NockEval s f (.val p)) :
    ∃ ep, Enc p ep ∧ WSteps (share (compiled f s)) ep :=
  let ⟨ep, hp, he⟩ := compiled_value h
  ⟨ep, hp, (share_red _).trans he⟩

/-- **`shared_crash`**: the shared program reduces to `Err` on a crash. -/
theorem shared_crash {s f : Noun} (h : NockEval s f .exit) : WSteps (share (compiled f s)) errT :=
  (share_red _).trans (compiled_crash h)

-- ---------------------------------------------------------------------------
-- Encodings are weak head normal forms; the join to the circuit
-- ---------------------------------------------------------------------------

theorem whnf_atomT (b : Term) : Whnf (atomT b) := .S2 _ _
theorem whnf_cellT (h t : Term) : Whnf (cellT h t) := .K1 _
theorem whnf_formT (h t k : Term) : Whnf (formT h t k) := .K1 _
theorem whnf_errT : Whnf errT := .K1 _

/-- **`enc_whnf`**: an encoding of a noun is a weak head normal form. -/
theorem enc_whnf {p : Noun} {ep : Term} (h : Enc p ep) : Whnf ep := by
  cases h with
  | atom n => exact whnf_atomT _
  | cell _ _ => exact whnf_cellT _ _
  | form _ _ => exact whnf_formT _ _ _

/-- The weak head normal form that a term reaches weakly reduces to any
    weak head normal form it weakly reduces to (lean-ski's `eval_back`
    and `Eval.deterministic`). -/
theorem eval_wsteps {t u v : Term} (hu : Whnf u) (ht : WSteps t u) (hv : Eval t v) : WSteps v u := by
  obtain ⟨v', hv', hw⟩ := eval_back ht ⟨.refl u, hu⟩
  rw [Eval.deterministic hv hv']
  exact hw

/-- **`eval_enc`**: a term that weakly reduces to an encoding has that
    encoding, up to reduction inside its fields, as its weak head normal
    form. -/
theorem eval_enc {t v : Term} {p : Noun} {ep : Term} (he : Enc p ep) (ht : WSteps t ep)
    (hv : Eval t v) : WSteps v ep :=
  eval_wsteps (enc_whnf he) ht hv

/-- **The row's statement.**  `Eval (share (compiled f s)) v` is what
    `Circuit.export_sound` gives for an accepted proof of the row; its
    final state `v` weakly reduces to an encoding of Nock's product. -/
theorem shared_value_eval {s f p : Noun} {v : Term} (h : NockEval s f (.val p))
    (hv : Eval (share (compiled f s)) v) : ∃ ep, Enc p ep ∧ WSteps v ep :=
  let ⟨ep, hp, he⟩ := shared_value h
  ⟨ep, hp, eval_enc hp he hv⟩

theorem shared_crash_eval {s f : Noun} {v : Term} (h : NockEval s f .exit)
    (hv : Eval (share (compiled f s)) v) : WSteps v errT :=
  eval_wsteps whnf_errT (shared_crash h) hv

/-- The same for the unshared row `compiled f s`. -/
theorem compiled_value_eval {s f p : Noun} {v : Term} (h : NockEval s f (.val p))
    (hv : Eval (compiled f s) v) : ∃ ep, Enc p ep ∧ WSteps v ep :=
  let ⟨ep, hp, he⟩ := compiled_value h
  ⟨ep, hp, eval_enc hp he hv⟩

theorem compiled_crash_eval {s f : Noun} {v : Term} (h : NockEval s f .exit)
    (hv : Eval (compiled f s) v) : WSteps v errT :=
  eval_wsteps whnf_errT (compiled_crash h) hv

end Nock2Ski
