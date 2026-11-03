import Nock2Ski.Compile
import Ski.Fuel

/-!
# normcheck: the reference tests through the Lean compiler

`lake exe normcheck` runs every triple of urbit/benchmark's
`norm/tests.json` (63 tests over autocons and opcodes 0–11, transcribed
below) through `Nock2Ski.compiled` and lean-ski's `runF`, reads the
product back, and compares it with the reference result; a crash in the
reference (`result: null`) must come back as `Err`.  A small fuelled
reference evaluator in lean-nock's order (`nockRef`; lean-nock's own
`nockF` cannot be imported beside `Ski.Basic`, both define a top-level
`Diverges`) is run on the same triples as a check on the transcription.

The product is read behaviourally, as `python/skinock/run.py` reads it:
the term is applied to one fresh variable per constructor of the noun sum
(`OTerm.var`, inert under reduction) and head-reduced; the variable at the
head of the spine says which constructor the value is, and its arguments
are read the same way, bits included.  Reading forces the whole noun, so a
crash anywhere in it is the `Err` marker.  This is `Ski/Open.lean`'s
probing idiom made executable; nothing here is proved, the exe is a gate.
-/

open Nock2Ski Term

namespace NormCheck

-- ---------------------------------------------------------------------------
-- `[a b c]` notation
-- ---------------------------------------------------------------------------

/-- Parse `[a b c]` notation, right-nested; digits may carry dots. -/
partial def parseNoun (s : String) : Except String Noun :=
  let toks := (s.replace "[" " [ " |>.replace "]" " ] ").splitOn " " |>.filter (· ≠ "")
  let rec item : List String → Except String (Noun × List String)
    | [] => .error "unexpected end"
    | "[" :: rest => do
      let rec items (ts : List String) (acc : List Noun) : Except String (List Noun × List String) :=
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
        .ok (before.foldl (fun acc x => Noun.cell x acc) last, r)
    | "]" :: _ => .error "unexpected ]"
    | t :: rest =>
      match (t.replace "." "").toNat? with
      | some n => .ok (Noun.atom n, rest)
      | none => .error s!"not a number: {t}"
  match item toks with
  | .ok (n, []) => .ok n
  | .ok (_, _) => .error "trailing input"
  | .error e => .error e

partial def showNoun : Noun → String
  | .atom n => toString n
  | .cell h t =>
    let rec parts : Noun → List String
      | .cell h t => showNoun h :: parts t
      | n => [showNoun n]
    "[" ++ " ".intercalate (showNoun h :: parts t) ++ "]"

-- ---------------------------------------------------------------------------
-- Head reduction of open terms, with fuel
-- ---------------------------------------------------------------------------

/-- The computable contraction at the head of the spine, `step?` for open
    terms: a variable is inert. -/
def ostep? : OTerm → Option OTerm
  | .app f x =>
    match ostep? f with
    | some f' => some (.app f' x)
    | none =>
      match f with
      | .I => some x
      | .app .K y => some y
      | .app (.app .S y) z => some (.app (.app y x) (.app z x))
      | _ => none
  | _ => none

/-- Head-reduce with fuel; the contraction count is accumulated. -/
def owhnf (count : IO.Ref Nat) : Nat → OTerm → IO (Option OTerm)
  | 0, _ => pure none
  | k + 1, t =>
    match ostep? t with
    | none => pure (some t)
    | some t' => do count.modify (· + 1); owhnf count k t'

def spine : OTerm → OTerm × List OTerm
  | .app f x => let (h, as) := spine f; (h, as ++ [x])
  | t => (t, [])

-- ---------------------------------------------------------------------------
-- Reading a noun back
-- ---------------------------------------------------------------------------

/-- Markers: one fresh variable per constructor. -/
def mAtom : OTerm := .var 0
def mCell : OTerm := .var 1
def mForm : OTerm := .var 2
def mErr : OTerm := .var 3
def mNil : OTerm := .var 4
def mCons : OTerm := .var 5
def mT : OTerm := .var 6
def mF : OTerm := .var 7

inductive Read
  | val (n : Noun)
  | crash
  | fuel
  | bad (msg : String)

def FUEL : Nat := 50_000_000

partial def readBit (count : IO.Ref Nat) (t : OTerm) : IO (Except Read Bool) := do
  match ← owhnf count FUEL (t ⬝ₒ mT ⬝ₒ mF) with
  | none => pure (.error .fuel)
  | some u =>
    match spine u with
    | (.var 6, []) => pure (.ok true)
    | (.var 7, []) => pure (.ok false)
    | _ => pure (.error (.bad "not a bit"))

partial def readBits (count : IO.Ref Nat) (t : OTerm) (acc : Nat) (k : Nat) :
    IO (Except Read Nat) := do
  match ← owhnf count FUEL (t ⬝ₒ mNil ⬝ₒ mCons) with
  | none => pure (.error .fuel)
  | some u =>
    match spine u with
    | (.var 4, []) => pure (.ok acc)
    | (.var 5, [b, rest]) =>
      match ← readBit count b with
      | .error e => pure (.error e)
      | .ok bit => readBits count rest (if bit then acc + (1 <<< k) else acc) (k + 1)
    | _ => pure (.error (.bad "not bits"))

partial def readNoun (count : IO.Ref Nat) (t : OTerm) : IO Read := do
  match ← owhnf count FUEL (t ⬝ₒ mAtom ⬝ₒ mCell ⬝ₒ mForm ⬝ₒ mErr) with
  | none => pure .fuel
  | some u =>
    match spine u with
    | (.var 0, [b]) =>
      match ← readBits count b 0 0 with
      | .ok n => pure (.val (.atom n))
      | .error e => pure e
    | (.var 1, [h, tl]) | (.var 2, [h, tl, _]) =>
      match ← readNoun count h with
      | .val hn =>
        match ← readNoun count tl with
        | .val tn => pure (.val (.cell hn tn))
        | r => pure r
      | r => pure r
    | (.var 3, []) => pure .crash
    | _ => pure (.bad "not a noun")

-- ---------------------------------------------------------------------------
-- A reference evaluator over lean-nock's primitives, in its order
-- ---------------------------------------------------------------------------

/-- `some (some n)` a value, `some none` a crash, `none` out of fuel. -/
def nockRef : Nat → Noun → Noun → Option (Option Noun)
  | 0, _, _ => none
  | k + 1, a, f =>
    if Malformed f then some none else
    match f with
    | .cell (.cell b c) d => do
      let r1 ← nockRef k a (.cell b c)
      match r1 with
      | none => some none
      | some r1 => do
        let r2 ← nockRef k a d
        pure (r2.map (Noun.cell r1))
    | .cell (.atom 0) b => some (fasO b a)
    | .cell (.atom 1) b => some (some b)
    | .cell (.atom 2) (.cell b c) => do
      let r1 ← nockRef k a b
      match r1 with
      | none => some none
      | some r1 => do
        let r2 ← nockRef k a c
        match r2 with
        | none => some none
        | some r2 => nockRef k r1 r2
    | .cell (.atom 3) b => do
      let r ← nockRef k a b
      pure (r.map wut)
    | .cell (.atom 4) b => do
      let r ← nockRef k a b
      pure (r.bind lusO)
    | .cell (.atom 5) (.cell b c) => do
      let r1 ← nockRef k a b
      match r1 with
      | none => some none
      | some r1 => do
        let r2 ← nockRef k a c
        pure (r2.map (tisN r1))
    | .cell (.atom 6) (.cell b (.cell c d)) => do
      let r ← nockRef k a b
      match r with
      | some (.atom 0) => nockRef k a c
      | some (.atom 1) => nockRef k a d
      | _ => some none
    | .cell (.atom 7) (.cell b c) => do
      let r ← nockRef k a b
      match r with
      | none => some none
      | some r => nockRef k r c
    | .cell (.atom 8) (.cell b c) => do
      let r ← nockRef k a b
      match r with
      | none => some none
      | some r => nockRef k (.cell r a) c
    | .cell (.atom 9) (.cell b c) => do
      let r ← nockRef k a c
      match r with
      | none => some none
      | some core =>
        match fasO b core with
        | none => some none
        | some arm => nockRef k core arm
    | .cell (.atom 10) (.cell (.cell b c) d) => do
      let r2 ← nockRef k a d
      match r2 with
      | none => some none
      | some r2 => do
        let r1 ← nockRef k a c
        match r1 with
        | none => some none
        | some r1 => some (haxO b r1 r2)
    | .cell (.atom 11) (.cell (.atom _) c) => nockRef k a c
    | .cell (.atom 11) (.cell (.cell _ c) d) => do
      let r ← nockRef k a c
      match r with
      | none => some none
      | some _ => nockRef k a d
    | _ => some none

-- ---------------------------------------------------------------------------
-- The tests: urbit/benchmark norm/tests.json, (subject, formula, result)
-- ---------------------------------------------------------------------------

/-- `(opcode, subject, formula, result)`; `none` is a crash. -/
def tests : List (String × String × String × Option String) := [
  ("autocons", "42", "[[4 0 1] [0 1]]", some "[43 42]"),
  ("autocons", "[1 2]", "[[0 2] [0 3] [0 1]]", some "[1 2 1 2]"),
  ("0", "42", "[0 1]", some "42"),
  ("0", "[1 2]", "[0 2]", some "1"),
  ("0", "[1 2]", "[0 3]", some "2"),
  ("0", "[[1 2] [3 4]]", "[0 4]", some "1"),
  ("0", "[[1 2] [3 4]]", "[0 5]", some "2"),
  ("0", "[[1 2] [3 4]]", "[0 6]", some "3"),
  ("0", "[[1 2] [3 4]]", "[0 7]", some "4"),
  ("0", "[[[1 2] [3 4]] [[5 6] [7 8]]]", "[0 12]", some "5"),
  ("0", "[[[1 2] [3 4]] [[5 6] [7 8]]]", "[0 15]", some "8"),
  ("0", "42", "[0 0]", none),
  ("0", "[1 2]", "[0 6]", none),
  ("1", "42", "[1 0]", some "0"),
  ("1", "42", "[1 57]", some "57"),
  ("1", "0", "[1 [1 2]]", some "[1 2]"),
  ("1", "0", "[1 [[1 2] [3 4]]]", some "[[1 2] 3 4]"),
  ("1", "[[99 100] [101 102]]", "[1 0]", some "0"),
  ("2", "42", "[2 [0 1] [1 [4 0 1]]]", some "43"),
  ("2", "0", "[2 [1 [1 2]] [1 [1 3]]]", some "3"),
  ("2", "[[4 0 1] 99]", "[2 [0 3] [0 2]]", some "100"),
  ("2", "42", "[2 [1 0] [1 [4 0 1]]]", some "1"),
  ("3", "[1 2]", "[3 [0 1]]", some "0"),
  ("3", "42", "[3 [0 1]]", some "1"),
  ("3", "0", "[3 [1 [1 2]]]", some "0"),
  ("3", "0", "[3 [1 42]]", some "1"),
  ("4", "42", "[4 0 1]", some "43"),
  ("4", "0", "[4 0 1]", some "1"),
  ("4", "[1 2]", "[4 0 3]", some "3"),
  ("4", "0", "[4 4 0 1]", some "2"),
  ("4", "[1 2]", "[4 0 1]", none),
  ("5", "42", "[5 [0 1] [0 1]]", some "0"),
  ("5", "42", "[5 [0 1] [1 43]]", some "1"),
  ("5", "[[1 2] [1 2]]", "[5 [0 2] [0 3]]", some "0"),
  ("5", "[[1 2] [3 4]]", "[5 [0 2] [0 3]]", some "1"),
  ("5", "[42 [1 2]]", "[5 [0 2] [0 3]]", some "1"),
  ("6", "42", "[6 [1 0] [1 1] [1 2]]", some "1"),
  ("6", "42", "[6 [1 1] [1 1] [1 2]]", some "2"),
  ("6", "[1 2]", "[6 [3 [0 1]] [1 99] [0 2]]", some "99"),
  ("6", "42", "[6 [3 [0 1]] [1 99] [0 1]]", some "42"),
  ("6", "42", "[6 [1 2] [1 1] [1 2]]", none),
  ("7", "42", "[7 [4 0 1] [4 0 1]]", some "44"),
  ("7", "[1 2]", "[7 [0 2] [4 0 1]]", some "2"),
  ("7", "42", "[7 [1 [1 2]] [0 2]]", some "1"),
  ("7", "0", "[7 [4 0 1] [7 [4 0 1] [4 0 1]]]", some "3"),
  ("8", "42", "[8 [4 0 1] [0 2]]", some "43"),
  ("8", "42", "[8 [4 0 1] [0 3]]", some "42"),
  ("8", "42", "[8 [1 0] [5 [0 2] [0 3]]]", some "1"),
  ("8", "[1 2]", "[8 [1 99] [0 2]]", some "99"),
  ("8", "42", "[8 [4 0 1] [[0 2] [0 3]]]", some "[43 42]"),
  ("9", "0", "[9 2 [1 [[4 0 3] 42]]]", some "43"),
  ("9", "0", "[9 2 [1 [[0 3] 99]]]", some "99"),
  ("9", "0", "[9 2 [10 [3 [1 7]] [1 [[4 0 3] 42]]]]", some "8"),
  ("9", "[[4 0 3] 0]", "[9 2 [0 1]]", some "1"),
  ("10", "[1 2]", "[10 [2 [1 3]] [0 1]]", some "[3 2]"),
  ("10", "[1 2]", "[10 [3 [1 3]] [0 1]]", some "[1 3]"),
  ("10", "[1 2]", "[10 [1 [1 99]] [0 1]]", some "99"),
  ("10", "[[1 2] [3 4]]", "[10 [4 [1 99]] [0 1]]", some "[[99 2] 3 4]"),
  ("10", "[[1 2] [3 4]]", "[10 [7 [1 99]] [0 1]]", some "[[1 2] 3 99]"),
  ("11", "42", "[11 1 [4 0 1]]", some "43"),
  ("11", "[1 2]", "[11 37 [0 2]]", some "1"),
  ("11", "42", "[11 [1 [1 0]] [4 0 1]]", some "43"),
  ("11", "[1 2]", "[11 [1 [4 0 2]] [0 3]]", some "2")]

/-- The M2 gate programs of `PLAN.md` §1 and §8: the spec's count-up `dec`,
    and Hoon's compiled `++dec` (lean-nock's `HoonOne.decBat`) called on a
    gate in the subject and on a gate pushed by `[1 …]` in the formula. -/
def decBat : String :=
  "[11 [1851876717 [1 [1 1717658988] [7 [[0 1] [8 [1 [1 [100 [101 [99 [114 [101 [109 [101 [110 [116 [45 [117 [110 [100 [101 [114 [102 [108 [111 [119 0]]]]]]]]]]]]]]]]]]]]] [9 2 [0 1]]]]] [0 1]]] [6 [5 [1 0] [0 6]] [0 0] [8 [1 0] [8 [1 6 [5 [0 30] 4 0 6] [0 6] 9 2 [10 [6 4 0 6] 0 1]] [9 2 0 1]]]]]"

def countUp : String := "[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]"

def programs : List (String × String × String × Option String) := [
  ("count-up dec", "7", countUp, some "6"),
  ("count-up dec", "1", countUp, some "0"),
  ("hoon dec, gate in the subject", s!"[{decBat} 0 0]", "[9 2 [10 [6 [1 5]] [0 1]]]", some "4"),
  ("hoon dec, gate in the subject", s!"[{decBat} 0 0]", "[9 2 [10 [6 [1 0]] [0 1]]]", none),
  ("hoon dec, gate pushed by [1 …]", "0", s!"[7 [1 [{decBat} 0 0]] [9 2 [10 [6 [1 12]] [0 1]]]]", some "11"),
  ("hoon dec, gate pushed by [1 …]", "0", s!"[7 [1 [{decBat} 0 0]] [9 2 [10 [6 [1 0]] [0 1]]]]", none)]

-- ---------------------------------------------------------------------------
-- The run
-- ---------------------------------------------------------------------------

def showOutcome : Option Noun → String
  | none => "crash"
  | some n => showNoun n

def readToOutcome : Read → Except String (Option Noun)
  | .val n => .ok (some n)
  | .crash => .ok none
  | .fuel => .error "FUEL"
  | .bad m => .error m

def refOutcome : Option (Option Noun) → Except String (Option Noun)
  | some o => .ok o
  | none => .error "FUEL"

def runOne (i : Nat) (t : String × String × String × Option String) : IO Bool := do
  let (op, s, f, r) := t
  let parsed : Except String (Noun × Noun × Option Noun) := do
    let sn ← parseNoun s
    let fn ← parseNoun f
    let rn ← match r with
      | none => pure none
      | some rs => (parseNoun rs).map some
    pure (sn, fn, rn)
  match parsed with
  | .error e =>
    IO.println s!"FAIL #{i} op {op}: parse error {e}"
    pure false
  | .ok (sn, fn, want) =>
    let count ← IO.mkRef 0
    let term := compiled fn sn
    -- lean-ski's `runF` to weak head normal form first (the closed run), then
    -- the behavioural read-out at fresh variables
    let head := match runF FUEL term with
      | some (_, k) => s!"{k} head contractions"
      | none => "FUEL at the head"
    let got ← readNoun count term.toO
    let steps ← count.get
    let gotO := readToOutcome got
    let nf := refOutcome (nockRef 100000 sn fn)
    let okSki := match gotO with | .ok o => o == want | .error _ => false
    let okNock := match nf with | .ok o => o == want | .error _ => false
    let ok := okSki && okNock
    let gotS := match gotO with | .ok o => showOutcome o | .error e => e
    let nfS := match nf with | .ok o => showOutcome o | .error e => e
    IO.println s!"{if ok then "ok  " else "FAIL"} #{i} op {op}: *[{s} {f}] = {showOutcome want}; ski {gotS} ({head}, {steps} with the read-out); ref {nfS}"
    pure ok

def main : IO UInt32 := do
  let mut good := 0
  let mut i := 0
  for t in tests do
    if ← runOne i t then good := good + 1
    i := i + 1
  IO.println s!"norm: {good}/{tests.length} agree (the Lean compiler, read back by probing; the reference evaluator)"
  let mut goodP := 0
  let mut j := 0
  for t in programs do
    if ← runOne j t then goodP := goodP + 1
    j := j + 1
  IO.println s!"programs: {goodP}/{programs.length} agree"
  pure (if good == tests.length && goodP == programs.length then 0 else 1)

end NormCheck

def main : IO UInt32 := NormCheck.main
