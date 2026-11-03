import Nock2Ski.Share
import Ski.Fuel
import Nock2Ski.NounText

open Nock

/-!
# nockstatement: a Nock program as a corpus row for lean-ski's circuit

`lake exe nockstatement NAME FORMULA SUBJECT` parses the two nouns, builds
`compiled f s = nockToSki f ⬝ encLit s` and its sharing `share (compiled f
s)` (`Nock2Ski/Share.lean`: the repeated subterms bound once, so the
prefix tree is the DAG's size; `--unshared` keeps `compiled f s`), runs it
to weak head normal form with lean-ski's `runF`, counting head
contractions (the βs of the sharing included, as ski-air's machine counts
them), and prints the corpus row ski-air reads (lean-ski's `bench/Dump.lean`
format):

    NAME COUNT PREFIXTERM

the term in prefix form with a backtick for application.  The count is the
one ski-air's own machine checks against before it proves a row: a
contraction of `S`, `K` or `I` at the head of the spine (`Run.contractions`
in `bench/plonky3/src/main.rs`; the machine's `App` unwinding steps are
rows, not contractions).  `runF`'s `step?` contracts the same redex, so the
two counts agree; `--count-term` on `release/sumto/sumto_us.term` prints
lean-ski's reference 10297 as the calibration.

`lake exe nockstatement --check [--unshared] NAME FORMULA SUBJECT <
corpus.txt` recomputes the row from the formula and the subject and
compares it with the row of that name on stdin, count and term; exit 1 on
a mismatch, 2 on a usage or parse error.  This is the verifier's Lean
check: the term is never trusted from a file, and `shared_value`
(`compiled_value` for `--unshared`) is the theorem about the term it
recomputes.

`lake exe nockstatement --count-term FILE` reads a prefix term and prints
its head contraction count (the calibration above).

`lake exe nockstatement --cells FORMULA SUBJECT [MINSIZE…]` prints the
cells of `compiled f s` and of `shareT m (compiled f s)` at each threshold
`m` (default: `shareMin` and a sweep), with the bindings and the
contraction count of each: the sizing behind `shareMin`, run before
ski-air is.
-/

open Nock2Ski Term Nock2Ski.NounText

namespace NockStatement

/-- lean-ski's `Dump.lean` printing, iteratively: a backtick for
    application.  The compiled terms are large and deep. -/
def prefixOf (t : Term) : String := Id.run do
  let mut out : String := ""
  let mut stack : List Term := [t]
  repeat
    match stack with
    | [] => break
    | u :: rest =>
      match u with
      | .S => out := out.push 'S'; stack := rest
      | .K => out := out.push 'K'; stack := rest
      | .I => out := out.push 'I'; stack := rest
      | .app f a => out := out.push '`'; stack := f :: a :: rest
  return out

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

/-- Parse the prefix form, iteratively (right to left, a stack of terms). -/
def parsePrefix (s : String) : Except String Term := do
  let mut stack : List Term := []
  for c in s.toList.reverse do
    match c with
    | 'S' => stack := .S :: stack
    | 'K' => stack := .K :: stack
    | 'I' => stack := .I :: stack
    | '`' =>
      match stack with
      | f :: a :: rest => stack := (f ⬝ a) :: rest
      | _ => throw "a backtick without two operands"
    | c => if c.isWhitespace then pure () else throw s!"bad term character {repr c}"
  match stack with
  | [t] => pure t
  | [] => throw "empty term"
  | _ => throw "trailing operands"

/-- Fuel for the run: each unit is one head contraction. -/
def FUEL : Nat := 1 <<< 26

/-- Head contractions to weak head normal form, `none` out of fuel. -/
def countOf (t : Term) : Option Nat := (runF FUEL t).map (·.2)

/-- A corpus name is an identifier, as ski-air and lean-ski's release take it. -/
def isName (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => c.isAlphanum || c == '_')

structure Row where
  name : String
  count : Nat
  term : String

/-- The row of `name` on stdin, split as ski-air's `lean_words` splits it. -/
def findRow (input : String) (name : String) : Option Row := Id.run do
  for line in input.splitOn "\n" do
    match line.splitOn " " |>.filter (· ≠ "") with
    | [n, c, t] =>
      if n == name then
        if let some k := c.toNat? then return some ⟨n, k, t⟩
    | _ => pure ()
  return none

def usage : String :=
  "usage: nockstatement [--unshared] NAME FORMULA SUBJECT\n       nockstatement --check [--unshared] NAME FORMULA SUBJECT < corpus.txt\n       nockstatement --count-term FILE\n       nockstatement --cells FORMULA SUBJECT [MINSIZE...]"

def die (msg : String) (code : UInt32 := 2) : IO UInt32 := do
  IO.eprintln msg
  pure code

/-- The two nouns of a program. -/
def parseProgram (formula subject : String) : IO (Except String (Noun × Noun)) := do
  let f ← match parseNoun formula with
    | .ok f => pure f
    | .error e => return .error s!"formula: {e}"
  let s ← match parseNoun subject with
    | .ok s => pure s
    | .error e => return .error s!"subject: {e}"
  if !isFormula f then IO.eprintln s!"note: {showNoun f} is not a formula; it compiles to the crash"
  return .ok (f, s)

/-- The row of a program: its count and prefix term, of `share (compiled f
    s)`, or of `compiled f s` when `shared` is off. -/
def rowOf (shared : Bool) (name formula subject : String) : IO (Except String Row) := do
  if !isName name then return .error s!"{name}: a name is letters, digits and underscores"
  let (f, s) ← match ← parseProgram formula subject with
    | .ok p => pure p
    | .error e => return .error e
  let t0 := compiled f s
  let t := if shared then share t0 else t0
  if shared then
    IO.eprintln s!"{name}: term of {treeSize t0} cells, shared {treeSize t} ({shareCount shareMin t0} bindings)"
  else
    IO.eprintln s!"{name}: term of {treeSize t0} cells, unshared"
  match countOf t with
  | none => return .error s!"{name}: no weak head normal form within {FUEL} contractions"
  | some k => return .ok ⟨name, k, prefixOf t⟩

/-- The depth of the term as a tree. -/
def depthOf (t : Term) : Nat := Id.run do
  let mut best := 0
  let mut stack : List (Term × Nat) := [(t, 1)]
  repeat
    match stack with
    | [] => break
    | (u, d) :: rest =>
      if d > best then best := d
      match u with
      | .app f a => stack := (f, d + 1) :: (a, d + 1) :: rest
      | _ => stack := rest
  return best

/-- `--cells`: the sizing of the sharing at each threshold. -/
def cells (formula subject : String) (mins : List Nat) : IO UInt32 := do
  let (f, s) ← match ← parseProgram formula subject with
    | .ok p => pure p
    | .error e => return ← die e
  let t0 := compiled f s
  let c0 := countOf t0
  IO.println s!"unshared: {treeSize t0} cells, depth {depthOf t0}, {c0.map toString |>.getD "no whnf"} contractions"
  for m in mins do
    let t := shareT m t0
    let c := countOf t
    IO.println s!"shareT {m}: {treeSize t} cells, depth {depthOf t}, {shareCount m t0} bindings, {c.map toString |>.getD "no whnf"} contractions{if m = shareMin then " (shareMin)" else ""}"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--count-term", file] =>
    let s ← IO.FS.readFile file
    match parsePrefix s with
    | .error e => die s!"{file}: {e}"
    | .ok t =>
      match countOf t with
      | none => die s!"{file}: no weak head normal form within {FUEL} contractions" 1
      | some k => IO.println s!"{k}"; pure 0
  | ["--cells", formula, subject] => cells formula subject [shareMin, 8, 16, 24, 48, 64, 96, 128, 256]
  | "--cells" :: formula :: subject :: mins =>
    match mins.mapM String.toNat? with
    | some ms => cells formula subject ms
    | none => die usage
  | [name, formula, subject] => emit true name formula subject
  | ["--unshared", name, formula, subject] => emit false name formula subject
  | ["--check", name, formula, subject] => check true name formula subject
  | ["--check", "--unshared", name, formula, subject] => check false name formula subject
  | _ => die usage
where
  emit (shared : Bool) (name formula subject : String) : IO UInt32 := do
    match ← rowOf shared name formula subject with
    | .error e => die e
    | .ok r => IO.println s!"{r.name} {r.count} {r.term}"; pure 0
  check (shared : Bool) (name formula subject : String) : IO UInt32 := do
    let input ← (← IO.getStdin).readToEnd
    let some given := findRow input name | die s!"{name}: no such row on stdin" 1
    match ← rowOf shared name formula subject with
    | .error e => die e
    | .ok r =>
      if r.count != given.count then
        die s!"{name}: count {given.count} given, {r.count} recomputed" 1
      else if r.term != given.term then
        die s!"{name}: the term given is not the formula's ({given.term.length} bytes given, {r.term.length} recomputed)" 1
      else
        IO.println s!"{name}: ok ({r.count} contractions, {r.term.length} bytes, {if shared then "shared, " else ""}recomputed from the formula)"
        pure 0

end NockStatement

def main (args : List String) : IO UInt32 := NockStatement.main args
