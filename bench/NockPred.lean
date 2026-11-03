import Nock2Ski.PredText
import Nock2Ski.NounText
import Ski.Fuel

/-!
# nockpred: a Nock program over a hidden atom as a predicate statement

The statement "I know an atom `n` of `K` bits with `*[n f] = p`", for the
public formula `f` and product `p`, on lean-ski's composed predicate
circuit (`Ski/Predicate.lean`, `Ski/Circuit/CompPred.lean`): the verifier
`nockPredV f K` (`Nock2Ski/Pred.lean`), the public `x = encNoun p`, and
`K` literal bits, the subject's, which the circuit constrains to `K` or
`K I` and keeps hidden.

- `nockpred [--log R M] NAME FORMULA PRODUCT K` prints `public.txt`: the
  statement in the format `ski-air composed-prove PUBLIC WITNESS PROOF`
  and `composed-verify PUBLIC PROOF` consume (lean-ski's
  `ComposedText.publicTextC`), at CPU and memory heights `2^R` and `2^M`
  (default 2^11, which no Nock program fits; `--log`).  Sizes to stderr.
- `nockpred --witness NAME SUBJECT K` prints the witness: the `K` bits of
  the atom `SUBJECT`, least significant first, one per line, then the
  one-cell region.  The prover keeps it.
- `nockpred --check NAME FORMULA PRODUCT K < public.txt` recomputes the
  verifier from the formula and compares: the statement on stdin must be
  `predicate (nockPredV f K) (encNoun p) K` over a one-cell region, and
  its text exactly the one Lean renders at its heights.  Exit 0 and a
  `STATEMENT` line, or 1.  The verifier's Lean check, as `skilark
  statement` is for SKIlark's predicate; ski-air's own call of lean-ski's
  `composed statement` is the second, independent check of the same bytes.
- `nockpred --run NAME FORMULA PRODUCT SUBJECT K` runs the verifier on the
  product and the subject's bits with lean-ski's `runF` and reports the
  head contraction count and whether it reaches `K`: the statement tried
  in the clear before it is proved.
- `nockpred --cells FORMULA K` prints the verifier's cells as a tree and
  shared.
-/

open Nock2Ski Nock2Ski.PredText Nock2Ski.NounText Term

namespace NockPred

def usage : String :=
  "usage: nockpred [--log R M] NAME FORMULA PRODUCT K       > public.txt\n" ++
  "       nockpred --witness NAME SUBJECT K                 > witness.txt\n" ++
  "       nockpred --check NAME FORMULA PRODUCT K           < public.txt\n" ++
  "       nockpred --run NAME FORMULA PRODUCT SUBJECT K\n" ++
  "       nockpred --cells FORMULA K"

def die (msg : String) (code : UInt32 := 2) : IO UInt32 := do
  IO.eprintln msg
  pure code

/-- Nodes of the term as a tree, the cells ski-air loads it into. -/
def treeSize (t : Term) : Nat := Id.run do
  let mut n := 0
  let mut stack : List Term := [t]
  repeat
    match stack with
    | [] => break
    | u :: rest =>
      n := n + 1
      match u with
      | .app f a => stack := f :: a :: rest
      | _ => stack := rest
  return n

def isName (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => c.isAlphanum || c == '_')

/-- The bit count: `1 ≤ K`, and `K + 1` private cells fit the circuit's
    `2^8` (`privateOK`); and at most 64, so `2^K` is a small number. -/
def parseK (k : String) : Except String Nat := do
  let some k := k.toNat? | throw s!"{k}: the bit count is not a number"
  if k = 0 then throw "the bit count is 0"
  if 64 < k then throw s!"the bit count {k} is above 64"
  if !privateOK k W then throw s!"{k} bits and a region of {W} are more than 2^8 private cells"
  pure k

/-- The statement's nouns: the formula and the product. -/
def parseStatement (formula product : String) : IO (Except String (Noun × Noun)) := do
  let f ← match parseNoun formula with
    | .ok f => pure f
    | .error e => return .error s!"formula: {e}"
  let p ← match parseNoun product with
    | .ok p => pure p
    | .error e => return .error s!"product: {e}"
  if !isFormula f then IO.eprintln s!"note: {showNoun f} is not a formula; it compiles to the crash"
  return .ok (f, p)

/-- The subject: an atom below `2^k`. -/
def parseSubject (subject : String) (k : Nat) : Except String Nat := do
  match parseNoun subject with
  | .error e => throw s!"subject: {e}"
  | .ok (.cell _ _) => throw "the subject is a cell; the statement hides an atom"
  | .ok (.atom n) =>
    if 2 ^ k ≤ n then throw s!"the subject {n} does not fit {k} bits"
    pure n

/-- The verifier, with its sizes to stderr. -/
def verifierOf (name : String) (f : Noun) (k : Nat) : IO Term := do
  let v0 := nockPredV0 f k
  let v := nockPredV f k
  IO.eprintln s!"{name}: verifier of {treeSize v0} cells, shared {treeSize v} ({shareCount shareMin v0} bindings); x = encNoun p"
  pure v

def emit (lg : Nat × Nat) (name formula product k : String) : IO UInt32 := do
  if !isName name then return ← die s!"{name}: a name is letters, digits and underscores"
  let k ← match parseK k with
    | .ok k => pure k
    | .error e => return ← die e
  if !logOK lg then return ← die s!"heights 2^{lg.1} and 2^{lg.2}: each log height is in [9, 20]"
  let (f, p) ← match ← parseStatement formula product with
    | .ok fp => pure fp
    | .error e => return ← die e
  let V ← verifierOf name f k
  let text := publicText V (encNoun p) k lg
  IO.eprintln s!"{name}: statement over {k} bits, heights 2^{lg.1} and 2^{lg.2}, {(text.splitOn "\n").length - 1} lines"
  IO.print text
  pure 0

def witness (name subject k : String) : IO UInt32 := do
  if !isName name then return ← die s!"{name}: a name is letters, digits and underscores"
  let k ← match parseK k with
    | .ok k => pure k
    | .error e => return ← die e
  let n ← match parseSubject subject k with
    | .ok n => pure n
    | .error e => return ← die e
  IO.print (witnessText (bitsK k n) [.S])
  pure 0

def check (name formula product k : String) : IO UInt32 := do
  if !isName name then return ← die s!"{name}: a name is letters, digits and underscores"
  let k ← match parseK k with
    | .ok k => pure k
    | .error e => return ← die e
  let (f, p) ← match ← parseStatement formula product with
    | .ok fp => pure fp
    | .error e => return ← die e
  let text ← (← IO.getStdin).readToEnd
  let h ← match parseHeader text with
    | .ok h => pure h
    | .error e => IO.println s!"NOT A PREDICATE STATEMENT: {e}"; return 1
  let V ← verifierOf name f k
  if h.n != k then IO.println s!"NOT THIS STATEMENT: over {h.n} bits, not {k}"; return 1
  if h.W != W then IO.println s!"NOT THIS STATEMENT: a region of {h.W} cells, not {W}"; return 1
  if !logOK h.lg then IO.println s!"NOT A STATEMENT: heights 2^{h.lg.1} and 2^{h.lg.2} out of [9, 20]"; return 1
  if h.x != encNoun p then IO.println s!"NOT THIS STATEMENT: x is not encNoun {showNoun p}"; return 1
  if h.V != V then IO.println s!"NOT THIS STATEMENT: the verifier is not nockPredV of {showNoun f} over {k} bits"; return 1
  if text != publicText V (encNoun p) k h.lg then
    IO.println "NOT A STATEMENT: the text is not the statement's (its heap is not the composed machine's)"; return 1
  IO.println s!"STATEMENT {name}: some {k} literal bits are an atom n with *[n {showNoun f}] = {showNoun p}, by eqn on nockToSki (heights 2^{h.lg.1} and 2^{h.lg.2})"
  pure 0

def FUEL : Nat := 1 <<< 26

def run (name formula product subject k : String) : IO UInt32 := do
  if !isName name then return ← die s!"{name}: a name is letters, digits and underscores"
  let k ← match parseK k with
    | .ok k => pure k
    | .error e => return ← die e
  let (f, p) ← match ← parseStatement formula product with
    | .ok fp => pure fp
    | .error e => return ← die e
  let n ← match parseSubject subject k with
    | .ok n => pure n
    | .error e => return ← die e
  let V ← verifierOf name f k
  let t := V ⬝ encNoun p ⬝ boolsT (bitsK k n)
  match runF FUEL t with
  | none => IO.println s!"{name}: no weak head normal form within {FUEL} contractions"; return 1
  | some (v, c) =>
    if v == K then
      IO.println s!"{name}: ACCEPTS in {c} contractions: the verifier reaches K on the {k} bits of {n} (bits {(bitsK k n).map fun b => if b then 1 else 0})"
      return 0
    else
      IO.println s!"{name}: REFUSES in {c} contractions: the verifier reaches {PredText.termText v |>.take 40}, not K"
      return 1

def cells (formula k : String) : IO UInt32 := do
  let k ← match parseK k with
    | .ok k => pure k
    | .error e => return ← die e
  let f ← match parseNoun formula with
    | .ok f => pure f
    | .error e => return ← die s!"formula: {e}"
  let c := nockToSki f
  let v0 := nockPredV0 f k
  IO.println s!"nockToSki f: {treeSize c} cells; eqnFix {treeSize eqnFix}; toBitsT {k}: {treeSize (toBitsT k)}"
  IO.println s!"verifier: {treeSize v0} cells as a tree, {treeSize (nockPredV f k)} shared ({shareCount shareMin v0} bindings at shareMin {shareMin})"
  pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--log", r, m, name, formula, product, k] =>
    match r.toNat?, m.toNat? with
    | some r, some m => emit (r, m) name formula product k
    | _, _ => die usage
  | ["--witness", name, subject, k] => witness name subject k
  | ["--check", name, formula, product, k] => check name formula product k
  | ["--run", name, formula, product, subject, k] => run name formula product subject k
  | ["--cells", formula, k] => cells formula k
  | [name, formula, product, k] => emit defaultLog name formula product k
  | _ => die usage

end NockPred

def main (args : List String) : IO UInt32 := NockPred.main args
