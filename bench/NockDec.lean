import Nock2Ski.DecTermNock
import Nock2Ski.DecLoop
import Nock2Ski.NounText
import Ski.Fuel
import Ski.Cost

/-!
# nockdec: the `dec` jet on lean-ski's circuit, for a Nock claim

`lake exe nockdec emit DIR NAME N [R M D]` writes the `decterm` statement
(`Nock2Ski/DecTermNock.lean`, lean-ski's `Ski/DecTermText.lean`) of the
claim `*[[N 0] phi(dec)] = [N-1 0]`: one verifier `λ β w. checkJ decF s p`,
the check `eqn (nockToSki decF ⬝ encNoun s) (encNoun p)` with every
occurrence of the compiled word replaced by the jet's atom, a region of one
cell, and the log heights `R M D` of the CPU, the memory and the jet's
table (default 12 12 9).  DIR/NAME.public.txt is the statement and
DIR/NAME.witness.txt the witness (the unused bit, the region's `K`).
`ski-air compd-prove` proves it; `nockdec_sound` is what an accepted proof
means.

`lake exe nockdec check NAME N PUBLIC` recomputes the statement from `N`
and the heights the text names, and compares it byte for byte: the
verifier's Lean half.  It also checks lean-ski's parser reads the text back
as exactly that verifier (`DecTerm.statementOfTextDG`).

`lake exe nockdec corpus NAME N` prints the base circuit's corpus row of the
same check unjetted, `checkT decF s p` (the bare word in the jet's place):
`NAME COUNT PREFIXTERM`, the row ski-air's base path proves.

`lake exe nockdec check-corpus NAME N < corpus.txt` recomputes that row
and compares it with the row of that name on stdin.

`lake exe nockdec loop-formula` prints the formula of the Λ loop `while
(top ≠ 0) dec` (`Nock2Ski/DecLoop.lean`), for `nockstatement`.

`lake exe nockdec probe N` runs the compiled loop on `[N [0 0]]` with every
occurrence of the compiled word replaced by the jet, in a head machine that
fires the jet only on a subject laid out as `encNn` (lean-ski's `decRow`
reads the memory cell by cell), and reports where the run stops.
-/

open Nock Nock2Ski Term Nock2Ski.NounText

namespace NockDec

def die (msg : String) (code : UInt32 := 2) : IO UInt32 := do IO.eprintln msg; pure code

def decS (n : Nat) : Noun := .cell (.atom n) (.atom 0)
def decP (n : Nat) : Noun := .cell (.atom (n - 1)) (.atom 0)

def defaultLogs : ComposedDText.DLogs := ⟨12, 12, 9⟩
def regionW : Nat := 1

def textOf (n : Nat) (lg : ComposedDText.DLogs) : String :=
  DecTerm.publicTextDG [nockDecV decF (decS n) (decP n)] regionW lg

def prefixOf (t : _root_.Term) : String := Id.run do
  let mut out : String := ""
  let mut stack : List _root_.Term := [t]
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

-- ---------------------------------------------------------------------------
-- The probe: a head machine with the jet firing on laid-out subjects only
-- ---------------------------------------------------------------------------

/-- Read a laid-out `encNn` back (up to `encNn`'s shape exactly). -/
partial def nnOf (t : OTerm) : Option DecJet.Nn :=
  match t with
  | .app (.app .S (.app .K .K)) (.app (.app .S (.app .K .K)) (.app (.app .S (.app .K .K)) (.app (.app .S .I) (.app .K b)))) =>
    (bitsOf b).map .atom
  | .app .K (.app (.app .S (.app .K .K)) (.app (.app .S (.app .K .K)) (.app (.app .S (.app (.app .S .I) (.app .K h))) (.app .K tl)))) =>
    match nnOf h, nnOf tl with
    | some a, some b => some (.cell a b)
    | _, _ => none
  | _ => none
where
  bitsOf : OTerm → Option (List Bool)
    | .K => some []
    | .app .K (.app (.app .S (.app (.app .S .I) (.app .K x))) (.app .K r)) =>
      let b := if x == .K then some true else if x == .app .K .I then some false else none
      match b, bitsOf r with
      | some b, some bs => some (b :: bs)
      | _, _ => none
    | _ => none

/-- Strip `K`-thunks: every `K x w` read as `x`, at the root and at every
    slot (route (B)'s reader; no `encNn` cell has that shape). -/
partial def unK : OTerm → OTerm
  | .app (.app .K x) _ => unK x
  | .app f x => .app (unK f) (unK x)
  | t => t

def osize : OTerm → Nat
  | .app f x => osize f + osize x
  | _ => 1

/-- The head of a term's spine and its argument count. -/
partial def spine : OTerm → OTerm × Nat
  | .app f _ => let (h, n) := spine f; (h, n + 1)
  | t => (t, 0)

def headName : OTerm → String
  | .S => "S" | .K => "K" | .I => "I" | .var _ => "J" | .app _ _ => "app"

/-- A short description of the argument the jet is handed. -/
def describe (x : OTerm) : String :=
  let (h, n) := spine x
  let kthunk := match x with | .app (.app .K _) _ => true | _ => false
  s!"spine head {headName h} with {n} arguments, size {osize x}" ++
    (if kthunk then ", a K-thunk K R w" else ", not a K-thunk") ++
    (match nnOf (unK x) with
      | some _ => ", readable after stripping K-thunks"
      | none => ", not readable after stripping K-thunks")

/-- `followK`: the jet also fires on a subject readable after `unK`. -/
partial def run (followK : Bool) (fuel : Nat) (t : OTerm) (stk : List OTerm) (n jets : Nat) : String :=
  if fuel = 0 then s!"no weak head normal form within the fuel ({n} contractions, {jets} jet steps)" else
  match t, stk with
  | .app f x, _ => run followK (fuel - 1) f (x :: stk) n jets
  | .I, x :: r => run followK (fuel - 1) x r (n + 1) jets
  | .K, x :: _ :: r => run followK (fuel - 1) x r (n + 1) jets
  | .S, f :: g :: x :: r => run followK (fuel - 1) f (x :: (.app g x) :: r) (n + 1) jets
  | .var j, x :: r =>
    match nnOf (if followK then unK x else x) with
    | some s => run followK (fuel - 1) (DecJet.encO (DecJet.decSpec s)).toO r (n + 1) (jets + 1)
    | none => s!"STOPPED at contraction {n} ({jets} jet steps before): the jet {j}'s argument is not an encNn laid out in memory"
  | _, _ => s!"weak head normal form after {n} contractions, {jets} jet steps"

def probe (n : Nat) : IO UInt32 := do
  let T := nockToSki decLoopF ⬝ encNoun (.cell (.atom n) (.cell (.atom 0) (.atom 0)))
  let TJ := abstJ (nockToSki decF) T
  IO.println s!"loop on [{n} [0 0]], the word's {TJ.count ComposedDText.JD} occurrences as the jet:"
  IO.println ("  " ++ run false (1 <<< 28) TJ [] 0 0)
  let C := checkJ decF (decS (max n 1)) (decP (max n 1))
  IO.println s!"the word alone on [{max n 1} 0] (the decterm statement's check):"
  IO.println ("  " ++ run false (1 <<< 28) C [] 0 0)
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir, name, n] => emit dir name n.toNat! defaultLogs
  | ["emit", dir, name, n, r, m, d] => emit dir name n.toNat! ⟨r.toNat!, m.toNat!, d.toNat!⟩
  | ["check", name, n, path] =>
    let text ← IO.FS.readFile path
    let some (Vs, W, lg) := DecTerm.statementOfTextDG text | die s!"{path}: not a decterm statement" 1
    let N := n.toNat!
    if W != regionW then die s!"{path}: region {W}, not {regionW}" 1
    else if text != textOf N lg then die s!"{path}: not the statement of *[[{N} 0] phi(dec)] = [{N - 1} 0]" 1
    else if Vs.length != 1 then die s!"{path}: {Vs.length} verifiers" 1
    else
      IO.println s!"{name}: ok, the decterm statement of *[[{N} 0] phi(dec)] = [{N - 1} 0] (heights {lg.rows} {lg.mem} {lg.dec}), recomputed"
      pure 0
  | ["corpus", name, n] =>
    let N := n.toNat!
    let t := checkT decF (decS N) (decP N)
    match runF (1 <<< 28) t with
    | none => die "no weak head normal form within the fuel" 1
    | some (_, k) => IO.println s!"{name} {k} {prefixOf t}"; pure 0
  | ["check-corpus", name, n] =>
    let input ← (← IO.getStdin).readToEnd
    let N := n.toNat!
    let t := checkT decF (decS N) (decP N)
    let some line := (input.splitOn "\n").find? (fun l => l.startsWith (name ++ " ")) | die s!"{name}: no such row on stdin" 1
    match runF (1 <<< 28) t with
    | none => die "no weak head normal form within the fuel" 1
    | some (_, k) =>
      if line != s!"{name} {k} {prefixOf t}" then die s!"{name}: not the row of the unjetted check at {N}" 1
      else IO.println s!"{name}: ok, the unjetted check of *[[{N} 0] phi(dec)] = [{N - 1} 0] ({k} contractions), recomputed"; pure 0
  | ["loop-formula"] => IO.println (showNoun decLoopF); pure 0
  | ["probe", n] => probe n.toNat!
  | _ => die "usage: nockdec emit DIR NAME N [R M D] | check NAME N PUBLIC | corpus NAME N | check-corpus NAME N < CORPUS | loop-formula | probe N"
where
  emit (dir name : String) (n : Nat) (lg : ComposedDText.DLogs) : IO UInt32 := do
    if n = 0 then die "N must be positive (the claim is about a decrement)" 1 else
    IO.FS.createDirAll dir
    IO.FS.writeFile s!"{dir}/{name}.public.txt" (textOf n lg)
    IO.FS.writeFile s!"{dir}/{name}.witness.txt" "0\nK\n"
    IO.println s!"wrote {dir}/{name}.public.txt: *[[{n} 0] phi(dec)] = [{n - 1} 0], heights {lg.rows} {lg.mem} {lg.dec}"
    pure 0

end NockDec

def main (args : List String) : IO UInt32 := NockDec.main args
