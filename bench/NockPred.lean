import Nock2Ski.PredText
import Nock2Ski.PredSkel
import Nock2Ski.NounText
import Ski.Fuel

open Nock

/-!
# nockpred: a Nock program over a hidden subject as a predicate statement

The statement "I know a subject `s` of the shape SKEL, its atoms hidden,
with `*[s f] = p`", for the public formula `f` and product `p`, on
lean-ski's composed predicate circuit (`Ski/Predicate.lean`,
`Ski/Circuit/CompPred.lean`).  SKEL is a public skeleton in noun notation
whose leaves are holes `?W`, a hidden atom of `W` bits each, or public
atoms: `8` (or `?8`) is one hidden atom of 8 bits, M4c's statement
(`nockPredV f 8`, `Nock2Ski/Pred.lean`); `[?4 ?4]` is a cell of two hidden
atoms of 4 bits each, M4d's (`nockPred2V f 4`, `Nock2Ski/PredSkel.lean`).
The verifier is `nockPredS f SKEL`, the public `x = encNoun p`, and the
circuit's literal bits, `N` of them (the holes' widths summed, laid out
left to right), are the subject's, constrained to `K` or `K I` and kept
hidden.

- `nockpred [--log R M] NAME FORMULA PRODUCT SKEL` prints `public.txt`:
  the statement in the format `ski-air composed-prove PUBLIC WITNESS
  PROOF` and `composed-verify PUBLIC PROOF` consume (lean-ski's
  `ComposedText.publicTextC`), at CPU and memory heights `2^R` and `2^M`
  (default 2^11, which no Nock program fits; `--log`).  Sizes to stderr.
- `nockpred --witness NAME SUBJECT SKEL` prints the witness: the bits of
  the subject's atoms under the skeleton, least significant first, hole by
  hole, one per line, then the one-cell region.  The prover keeps it.
- `nockpred --check NAME FORMULA PRODUCT SKEL < public.txt` recomputes the
  verifier from the formula and the skeleton and compares: the statement
  on stdin must be `predicate (nockPredS f SKEL) (encNoun p) N` over a
  one-cell region, and its text exactly the one Lean renders at its
  heights.  Exit 0 and a `STATEMENT` line, or 1.  The verifier's Lean
  check, as `skilark statement` is for SKIlark's predicate; ski-air's own
  call of lean-ski's `composed statement` is the second, independent
  check of the same bytes.
- `nockpred --run NAME FORMULA PRODUCT SUBJECT SKEL` runs the verifier on
  the product and the subject's bits with lean-ski's `runF` and reports
  the head contraction count and whether it reaches `K`: the statement
  tried in the clear before it is proved.
- `nockpred --cells FORMULA SKEL` prints the verifier's cells as a tree
  and shared.
-/

open Nock2Ski Nock2Ski.PredText Nock2Ski.NounText Term

namespace NockPred

def usage : String :=
  "usage: nockpred [--log R M] NAME FORMULA PRODUCT SKEL    > public.txt\n" ++
  "       nockpred --witness NAME SUBJECT SKEL              > witness.txt\n" ++
  "       nockpred --check NAME FORMULA PRODUCT SKEL        < public.txt\n" ++
  "       nockpred --run NAME FORMULA PRODUCT SUBJECT SKEL\n" ++
  "       nockpred --cells FORMULA SKEL\n" ++
  "SKEL: a hidden atom of W bits is ?W (a bare W is ?W); [?4 ?4] a cell of two; a bare\n" ++
  "      noun in a skeleton is public"

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

-- ---------------------------------------------------------------------------
-- Skeletons in text
-- ---------------------------------------------------------------------------

/-- Parse a skeleton: `[a b c]` notation, right-nested; `?W` a hole of `W`
    bits, digits a public atom; a bare number `W` is `?W`. -/
partial def parseSkel (s : String) : Except String Skel :=
  match s.toNat? with
  | some w => .ok (.hole w)
  | none =>
    let toks := (s.replace "[" " [ " |>.replace "]" " ] ").splitOn " " |>.filter (· ≠ "")
    let rec item : List String → Except String (Skel × List String)
      | [] => .error "unexpected end"
      | "[" :: rest => do
        let rec items (ts : List String) (acc : List Skel) : Except String (List Skel × List String) :=
          match ts with
          | "]" :: r => .ok (acc.reverse, r)
          | [] => .error "unclosed ["
          | _ => do
            let (n, r) ← item ts
            items r (n :: acc)
        let (xs, r) ← items rest []
        match xs.reverse with
        | [] | [_] => .error "a cell needs two parts"
        | last :: before =>
          .ok (before.foldl (fun acc x => Skel.cell x acc) last, r)
      | "]" :: _ => .error "unexpected ]"
      | t :: rest =>
        if t.startsWith "?" then
          match (t.drop 1).toNat? with
          | some w => .ok (.hole w, rest)
          | none => .error s!"not a hole: {t}"
        else
          match (t.replace "." "").toNat? with
          | some n => .ok (.lit (.atom n), rest)
          | none => .error s!"not a number or a hole: {t}"
    match item toks with
    | .ok (n, []) => .ok n
    | .ok (_, _) => .error "trailing input"
    | .error e => .error e

partial def showSkel : Skel → String
  | .hole w => s!"?{w}"
  | .lit n => showNoun n
  | .cell h t =>
    let rec parts : Skel → List String
      | .cell h t => showSkel h :: parts t
      | n => [showSkel n]
    "[" ++ " ".intercalate (showSkel h :: parts t) ++ "]"

/-- The holes' widths. -/
def holes : Skel → List Nat
  | .hole w => [w]
  | .lit _ => []
  | .cell l r => holes l ++ holes r

/-- The skeleton checked: at least one hole, each of 1 to 64 bits (so `2^W`
    is a small number), and `N + 1` private cells within the circuit's
    `2^8` (`privateOK`). -/
def parseSkeleton (s : String) : Except String Skel := do
  let sk ← match parseSkel s with
    | .ok sk => pure sk
    | .error e => throw s!"{s}: not a skeleton: {e}"
  let ws := holes sk
  if ws.isEmpty then throw s!"{showSkel sk}: a skeleton with no hole hides nothing"
  if ws.any (· = 0) then throw s!"{showSkel sk}: a hole of 0 bits"
  if ws.any (64 < ·) then throw s!"{showSkel sk}: a hole above 64 bits"
  if !privateOK sk.width W then
    throw s!"{showSkel sk}: {sk.width} bits and a region of {W} are more than 2^8 private cells"
  pure sk

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

/-- The subject's bits under the skeleton. -/
def parseSubject (subject : String) (sk : Skel) : Except String (Noun × List Bool) := do
  match parseNoun subject with
  | .error e => throw s!"subject: {e}"
  | .ok s =>
    match sk.bitsOf s with
    | .ok bs => pure (s, bs)
    | .error e => throw s!"subject {showNoun s} under {showSkel sk}: {e}"

/-- The verifier, with its sizes to stderr. -/
def verifierOf (name : String) (f : Noun) (sk : Skel) : IO Term := do
  let v0 := nockPredS0 f sk
  let v := nockPredS f sk
  IO.eprintln s!"{name}: verifier of {treeSize v0} cells, shared {treeSize v} ({shareCount shareMin v0} bindings); x = encNoun p; subject {showSkel sk}, {sk.width} bits"
  pure v

def emit (lg : Nat × Nat) (name formula product skel : String) : IO UInt32 := do
  if !isName name then return ← die s!"{name}: a name is letters, digits and underscores"
  let sk ← match parseSkeleton skel with
    | .ok sk => pure sk
    | .error e => return ← die e
  if !logOK lg then return ← die s!"heights 2^{lg.1} and 2^{lg.2}: each log height is in [9, 20]"
  let (f, p) ← match ← parseStatement formula product with
    | .ok fp => pure fp
    | .error e => return ← die e
  let V ← verifierOf name f sk
  let text := publicText V (encNoun p) sk.width lg
  IO.eprintln s!"{name}: statement over {sk.width} bits, heights 2^{lg.1} and 2^{lg.2}, {(text.splitOn "\n").length - 1} lines"
  IO.print text
  pure 0

def witness (name subject skel : String) : IO UInt32 := do
  if !isName name then return ← die s!"{name}: a name is letters, digits and underscores"
  let sk ← match parseSkeleton skel with
    | .ok sk => pure sk
    | .error e => return ← die e
  let (_, bs) ← match parseSubject subject sk with
    | .ok sb => pure sb
    | .error e => return ← die e
  IO.print (witnessText bs [.S])
  pure 0

def check (name formula product skel : String) : IO UInt32 := do
  if !isName name then return ← die s!"{name}: a name is letters, digits and underscores"
  let sk ← match parseSkeleton skel with
    | .ok sk => pure sk
    | .error e => return ← die e
  let (f, p) ← match ← parseStatement formula product with
    | .ok fp => pure fp
    | .error e => return ← die e
  let text ← (← IO.getStdin).readToEnd
  let h ← match parseHeader text with
    | .ok h => pure h
    | .error e => IO.println s!"NOT A PREDICATE STATEMENT: {e}"; return 1
  let V ← verifierOf name f sk
  if h.n != sk.width then IO.println s!"NOT THIS STATEMENT: over {h.n} bits, not {sk.width}"; return 1
  if h.W != W then IO.println s!"NOT THIS STATEMENT: a region of {h.W} cells, not {W}"; return 1
  if !logOK h.lg then IO.println s!"NOT A STATEMENT: heights 2^{h.lg.1} and 2^{h.lg.2} out of [9, 20]"; return 1
  if h.x != encNoun p then IO.println s!"NOT THIS STATEMENT: x is not encNoun {showNoun p}"; return 1
  if h.V != V then IO.println s!"NOT THIS STATEMENT: the verifier is not nockPredS of {showNoun f} over {showSkel sk}"; return 1
  if text != publicText V (encNoun p) sk.width h.lg then
    IO.println "NOT A STATEMENT: the text is not the statement's (its heap is not the composed machine's)"; return 1
  IO.println s!"STATEMENT {name}: some {sk.width} literal bits are the atoms of a subject s of shape {showSkel sk} with *[s {showNoun f}] = {showNoun p}, by eqn on nockToSki (heights 2^{h.lg.1} and 2^{h.lg.2})"
  pure 0

def FUEL : Nat := 1 <<< 26

def run (name formula product subject skel : String) : IO UInt32 := do
  if !isName name then return ← die s!"{name}: a name is letters, digits and underscores"
  let sk ← match parseSkeleton skel with
    | .ok sk => pure sk
    | .error e => return ← die e
  let (f, p) ← match ← parseStatement formula product with
    | .ok fp => pure fp
    | .error e => return ← die e
  let (s, bs) ← match parseSubject subject sk with
    | .ok sb => pure sb
    | .error e => return ← die e
  let V ← verifierOf name f sk
  let t := V ⬝ encNoun p ⬝ boolsT bs
  match runF FUEL t with
  | none => IO.println s!"{name}: no weak head normal form within {FUEL} contractions"; return 1
  | some (v, c) =>
    if v == K then
      IO.println s!"{name}: ACCEPTS in {c} contractions: the verifier reaches K on the {bs.length} bits of {showNoun s} under {showSkel sk} (bits {bs.map fun b => if b then 1 else 0})"
      return 0
    else
      IO.println s!"{name}: REFUSES in {c} contractions: the verifier reaches {PredText.termText v |>.take 40}, not K"
      return 1

def cells (formula skel : String) : IO UInt32 := do
  let sk ← match parseSkeleton skel with
    | .ok sk => pure sk
    | .error e => return ← die e
  let f ← match parseNoun formula with
    | .ok f => pure f
    | .error e => return ← die s!"formula: {e}"
  let c := nockToSki f
  let v0 := nockPredS0 f sk
  IO.println s!"nockToSki f: {treeSize c} cells; eqnFix {treeSize eqnFix}; subject {showSkel sk}: {treeSize (skelT sk.width sk 0 K) - 1} cells around the bits"
  IO.println s!"verifier: {treeSize v0} cells as a tree, {treeSize (nockPredS f sk)} shared ({shareCount shareMin v0} bindings at shareMin {shareMin})"
  pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--log", r, m, name, formula, product, skel] =>
    match r.toNat?, m.toNat? with
    | some r, some m => emit (r, m) name formula product skel
    | _, _ => die usage
  | ["--witness", name, subject, skel] => witness name subject skel
  | ["--check", name, formula, product, skel] => check name formula product skel
  | ["--run", name, formula, product, subject, skel] => run name formula product subject skel
  | ["--cells", formula, skel] => cells formula skel
  | [name, formula, product, skel] => emit defaultLog name formula product skel
  | _ => die usage

end NockPred

def main (args : List String) : IO UInt32 := NockPred.main args
