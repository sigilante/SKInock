import Nock2Ski.ProbeTree
import Ski.JetTable
import Ski.ProbeText
import Nock2Ski.NounText

/-!
# nockprobe: the public product as a probe plan, and the probe table checked

The probe step of the Nock rows (M4f, `Nock2Ski/ProbeTree.lean`,
`Nock2Ski/Probe.lean`).  This exe is on lean-ski's side of the two Lean
environments (it imports `Ski.AirProbe` and never `Nock.Eval`), so it can
compute the plan from the theorem's own tree and run lean-ski's checker.

- `nockprobe plan PRODUCT` prints the plan of `nounV p` (`nounPlan`,
  `Air.planOf (nounV p) 0`) in the format `lake exe jets plan` prints and
  ski-air's `probe.rs::parse_plan` and Avon's `witness --plan` read:
  `plan n`, then per segment `base k ctor arity parent field`.  The
  product is a noun in `[a b c]` notation; a product `crash` has no plan
  (the crash's tree `errV` is one segment with no fields, `nounV` never
  produces it: a row that crashes is proved by the base circuit's
  `shared_crash_eval`).
- `nockprobe tree PRODUCT` prints the tree itself, `nounV p`, as the
  outcome words ski-air's `probe-prove`, `probe-prove-table` and
  `probe-verify` and `lake exe jets plan` take (lean-ski's
  `probe-plan-file` branch, `Ski/ProbeText.lean`): `tree`, then the nodes
  in preorder, `c k n` each (`Probe.vWords`); `lake exe jets plan` of those
  words is this exe's plan.
- `nockprobe term CORPUS NAME` prints the row's term from the corpus
  (`NAME COUNT PREFIXTERM`), the file Avon and ski-air take.
- `nockprobe jets TERMFILE` prints the term's jet file (`JetTable.jetTable`
  over lean-ski's `allTemplates`, `tableText`), what `lake exe jets emit`
  writes for lean-ski's corpus: the roots the probe run may instantiate
  (none, for an unjetted Nock row whose term matches no template; then
  the file is `roots 0` and `jets 0`).
- `nockprobe check CORPUS NAME TABLE PRODUCT` checks a table with probe
  segments (the format of `lake exe jets check-probe`: the table, `starts
  N`, `fields n`): the table's term must be the corpus row's, and
  `Air.checkPA` must accept it for `nounPlan p` with the term's roots and
  jets.  `ACCEPT` means `Nock2Ski.probe_check`: the term's value is `p`
  (`ValueIs`), hence `probe_decodes_nock`: `*[s f] = p`.  Exit 1 otherwise.
-/

open Term Nock2Ski Nock2Ski.NounText Air JetTable Mach

namespace NockProbe

-- The table parsers, as lean-ski's bench/Jets.lean has them (an exe's, not
-- a library's, so copied).

partial def parseTerm (s : List Char) : Option (Term × List Char) :=
  match s with
  | 'S' :: r => some (.S, r)
  | 'K' :: r => some (.K, r)
  | 'I' :: r => some (.I, r)
  | '`' :: r =>
    match parseTerm r with
    | some (f, r1) =>
      match parseTerm r1 with
      | some (a, r2) => some (.app f a, r2)
      | none => none
    | none => none
  | _ => none

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

def parseCell (ws : List String) : Option Cell :=
  match ws with
  | ["S"] => some .S
  | ["K"] => some .K
  | ["I"] => some .I
  | ["N"] => some .nil
  | ["A", f, x] => do some (.app (← f.toNat?) (← x.toNat?))
  | ["C", x, r] => do some (.cons (← x.toNat?) (← r.toNat?))
  | ["X", n] => do some (.atom (← n.toNat?))
  | _ => none

def parseRow (ws : List String) : Option Air.Row :=
  match ws with
  | [h, s, c] => do some ⟨← h.toNat?, ← s.toNat?, ← c.toNat?⟩
  | _ => none

def parseTable (ls : List String) : Option (Term × Array Cell × List Air.Row) := do
  match ls with
  | tl :: nl :: rest =>
    let (t, r) ← parseTerm tl.trimAscii.toString.toList
    if !r.isEmpty then none
    let n ← nl.trimAscii.toString.toNat?
    let cells ← (rest.take n).mapM (fun l => parseCell (words l))
    if cells.length != n then none
    match rest.drop n with
    | kl :: rest2 =>
      let k ← kl.trimAscii.toString.toNat?
      let rows ← (rest2.take k).mapM (fun l => parseRow (words l))
      if rows.length != k then none
      if !(rest2.drop k).isEmpty then none
      some (t, cells.toArray, rows)
    | [] => none
  | _ => none

def parseProbe (ls : List String) : Option (Array Nat × Array (List Nat)) := do
  match ls with
  | sl :: rest =>
    let n ← match words sl with
      | ["starts", n] => n.toNat?
      | _ => none
    let starts ← (rest.take n).mapM (fun l => l.trimAscii.toString.toNat?)
    if starts.length != n then none
    match rest.drop n with
    | fl :: rest2 =>
      let m ← match words fl with
        | ["fields", m] => m.toNat?
        | _ => none
      let flds ← (rest2.take m).mapM fun l => do
        match (words l).mapM String.toNat? with
        | some (a :: ps) => if ps.length == a then some ps else none
        | _ => none
      if flds.length != m then none
      if !(rest2.drop m).isEmpty then none
      some (starts.toArray, flds.toArray)
    | [] => none
  | [] => none

/-- A plan's text, as `lake exe jets plan` prints it. -/
def planText (plan : List Seg) : String :=
  plan.foldl (fun s g => s ++ s!"{g.base} {g.k} {g.ctor} {g.arity} {g.parent} {g.field}\n")
    s!"plan {plan.length}\n"

def die (msg : String) (code : UInt32 := 1) : IO UInt32 := do
  IO.eprintln msg
  pure code

/-- The row `name` of a corpus: `NAME COUNT PREFIXTERM`. -/
def rowOf (corpus name : String) : IO (Except String String) := do
  if name.isEmpty || !name.all (fun c => c.isAlphanum || c == '_') then
    return .error s!"{name}: a name is letters, digits and underscores"
  let text ← IO.FS.readFile corpus
  for line in text.splitOn "\n" do
    match words line with
    | [n, _, t] => if n == name then return .ok t
    | _ => pure ()
  return .error s!"{name}: no such row in {corpus}"

def plan (product : String) : IO UInt32 := do
  match parseNoun product with
  | .error e => die s!"product: {e}" 2
  | .ok p =>
    let pl := nounPlan p
    IO.eprintln s!"{showNoun p}: {pl.length} segments, {kSum pl} markers"
    IO.print (planText pl)
    pure 0

def tree (product : String) : IO UInt32 := do
  match parseNoun product with
  | .error e => die s!"product: {e}" 2
  | .ok p =>
    let v := nounV p
    let ws := Probe.vWords v
    IO.eprintln s!"{showNoun p}: {ws.length / 3} nodes"
    IO.println ("tree " ++ " ".intercalate ws)
    pure 0

def term (corpus name : String) : IO UInt32 := do
  match ← rowOf corpus name with
  | .error e => die e
  | .ok t => IO.println t; pure 0

def jets (file : String) : IO UInt32 := do
  let text ← IO.FS.readFile file
  match parseTerm text.trimAscii.toString.toList with
  | some (t, []) =>
    let (roots, js) := jetTable (load t).heap allTemplates
    IO.eprintln s!"{file}: {roots.length} roots, {js.length} jets"
    IO.print (tableText roots js)
    pure 0
  | _ => die s!"{file}: not a prefix term" 2

def check (corpus name table product : String) : IO UInt32 := do
  let p ← match parseNoun product with
    | .error e => return ← die s!"product: {e}" 2
    | .ok p => pure p
  let rowText ← match ← rowOf corpus name with
    | .error e => return ← die e
    | .ok t => pure t
  let text ← IO.FS.readFile table
  let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let i := ls.findIdx (fun l => (words l).headD "" == "starts")
  match parseTable (ls.take i), parseProbe (ls.drop i) with
  | some (t, A, rows), some (starts, flds) =>
    -- the table's term is the row's: by text, as ski-air binds a proof to a row
    if (ls.headD "").trimAscii.toString != rowText then
      return ← die s!"REJECT {table}: its term is not the term of {name}"
    let pl := nounPlan p
    let (roots, js) := jetTable (load t).heap allTemplates
    if checkPA A t roots js pl starts flds rows.toArray then
      IO.println s!"ACCEPT {table}: the term of {name} has the value {showNoun p} ({rows.length} rows, {A.size} cells, {pl.length} segments, {roots.length} roots)"
      pure 0
    else
      die s!"REJECT {table}: not a probe table of {name} for {showNoun p}"
  | _, _ => die s!"MALFORMED {table}"

def usage : String :=
  "usage: nockprobe plan PRODUCT\n       nockprobe tree PRODUCT\n       nockprobe term CORPUS NAME\n       nockprobe jets TERMFILE\n       nockprobe check CORPUS NAME TABLE PRODUCT"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["plan", product] => plan product
  | ["tree", product] => tree product
  | ["term", corpus, name] => term corpus name
  | ["jets", file] => jets file
  | ["check", corpus, name, table, product] => check corpus name table product
  | _ => die usage 2

end NockProbe

def main (args : List String) : IO UInt32 := NockProbe.main args
