import Nock2Ski.Compile
import Ski.Fuel
import Nock2Ski.NounText

/-!
# nockstatement: a Nock program as a corpus row for lean-ski's circuit

`lake exe nockstatement NAME FORMULA SUBJECT` parses the two nouns, builds
`compiled f s = nockToSki f ⬝ encLit s`, runs it to weak head normal form
with lean-ski's `runF`, counting head contractions, and prints the corpus
row ski-air reads (lean-ski's `bench/Dump.lean` format):

    NAME COUNT PREFIXTERM

the term in prefix form with a backtick for application.  The count is the
one ski-air's own machine checks against before it proves a row: a
contraction of `S`, `K` or `I` at the head of the spine (`Run.contractions`
in `bench/plonky3/src/main.rs`; the machine's `App` unwinding steps are
rows, not contractions).  `runF`'s `step?` contracts the same redex, so the
two counts agree; `--count-term` on `release/sumto/sumto_us.term` prints
lean-ski's reference 10297 as the calibration.

`lake exe nockstatement --check NAME FORMULA SUBJECT < corpus.txt`
recomputes the row from the formula and the subject and compares it with
the row of that name on stdin, count and term; exit 1 on a mismatch, 2 on a
usage or parse error.  This is the verifier's Lean check: the term is
never trusted from a file, and `embed_value` (`Nock2Ski/Embed.lean`) is
the theorem about the term it recomputes.

`lake exe nockstatement --count-term FILE` reads a prefix term and prints
its head contraction count (the calibration above).
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
  "usage: nockstatement NAME FORMULA SUBJECT\n       nockstatement --check NAME FORMULA SUBJECT < corpus.txt\n       nockstatement --count-term FILE"

def die (msg : String) (code : UInt32 := 2) : IO UInt32 := do
  IO.eprintln msg
  pure code

/-- The row of a program: its count and prefix term. -/
def rowOf (name formula subject : String) : IO (Except String Row) := do
  if !isName name then return .error s!"{name}: a name is letters, digits and underscores"
  let f ← match parseNoun formula with
    | .ok f => pure f
    | .error e => return .error s!"formula: {e}"
  let s ← match parseNoun subject with
    | .ok s => pure s
    | .error e => return .error s!"subject: {e}"
  if !isFormula f then IO.eprintln s!"note: {showNoun f} is not a formula; it compiles to the crash"
  let t := compiled f s
  IO.eprintln s!"{name}: term of {treeSize t} nodes"
  match countOf t with
  | none => return .error s!"{name}: no weak head normal form within {FUEL} contractions"
  | some k => return .ok ⟨name, k, prefixOf t⟩

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
  | [name, formula, subject] =>
    match ← rowOf name formula subject with
    | .error e => die e
    | .ok r => IO.println s!"{r.name} {r.count} {r.term}"; pure 0
  | ["--check", name, formula, subject] =>
    let input ← (← IO.getStdin).readToEnd
    let some given := findRow input name | die s!"{name}: no such row on stdin" 1
    match ← rowOf name formula subject with
    | .error e => die e
    | .ok r =>
      if r.count != given.count then
        die s!"{name}: count {given.count} given, {r.count} recomputed" 1
      else if r.term != given.term then
        die s!"{name}: the term given is not the formula's ({given.term.length} bytes given, {r.term.length} recomputed)" 1
      else
        IO.println s!"{name}: ok ({r.count} contractions, {r.term.length} bytes, recomputed from the formula)"
        pure 0
  | _ => die usage

end NockStatement

def main (args : List String) : IO UInt32 := NockStatement.main args
