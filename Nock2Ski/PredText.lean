import Nock2Ski.Pred
import Ski.Statement

open Term Compose Stmt Mach

/-!
# The predicate statement's text, for `nockpred`

`public.txt` of a predicate statement as `ski-air composed-prove` and
`composed-verify` consume it and as lean-ski's `lake exe composed statement`
(`ComposedText.statementOfText`) accepts it: the header `predicate V x n`,
the region size, the heights, and the composed machine's heap with the
private cells blank.

These are copies of lean-ski's definitions (`Ski/Composed.lean`:
`BT.nleaves`, `pairO`, `encO`, `addStmts`, `cHeap`, `cMachine`;
`Ski/Predicate.lean`: `combBT`, `predStmt`; `Ski/ComposedText.lean`:
`termText`, `cellText`, `publicTextC`, `defaultLog`, `logOK`,
`privateOK`), since those modules cannot be imported beside lean-nock
(`Nock2Ski/Pred.lean`: the `Outcome` clash).  The text they render is
checked against the originals at every use: ski-air pipes the bytes of
`public.txt` to `lake exe composed statement -` in lean-ski before it
proves or verifies, and refuses anything that is not exactly
`publicTextC`'s text (`bench/plonky3/src/composed.rs`, `checked_public`).
`Ski.Statement`'s `slotHeap` and `pbuild` and `Ski.Heap`'s `build` are
lean-ski's own.
-/

namespace Nock2Ski.PredText

/-- `BT.nleaves`. -/
def nleaves : BT → Nat
  | .leaf _ => 1
  | .node l r => nleaves l + nleaves r

/-- `CompM.combBT`: the shape of `n` bits, a right comb, the last alone. -/
def combBT : Nat → BT
  | 0 => .leaf false
  | 1 => .leaf false
  | n + 2 => .node (.leaf false) (combBT (n + 1))

def pairO (a b : OTerm) : OTerm := .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ a)) ⬝ₒ (.K ⬝ₒ b)

/-- `Compose.encO`: the bits' encoding, leaf `i` the slot variable `i + 2`. -/
def encO : BT → Nat → OTerm
  | .leaf _, off => .var (off + 2)
  | .node l r, off => pairO (encO l off) (encO r (off + nleaves l))

/-- `CompM.predStmt`: `[ρ w] V x ρ`. -/
def predStmt (V x : Term) : Term := toTerm (absN [0, 1] (V.toO ⬝ₒ x.toO ⬝ₒ .var 0))

/-- `Compose.addStmts`: each term's cells, then `P ⬝ enc` and `(P ⬝ enc) ⬝ w`. -/
def addStmts (pe wr : Nat) : List Cell → List Term → List Cell × List Nat
  | h, [] => (h, [])
  | h, P :: Ps =>
    let (h2, pp) := build h P
    let h3 := h2 ++ [.app pp pe, .app h2.length wr]
    let (h4, roots) := addStmts pe wr h3 Ps
    (h4, (h2.length + 1) :: roots)

/-- `Compose.cHeap`: the composed machine's heap before its nil, and its roots. -/
def cHeap (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) : List Cell × List Nat :=
  let h0 := slotHeap ρ (nleaves shp) ++ region
  let e1 := pbuild (nleaves shp + 2) h0 (encO shp 0)
  addStmts e1.2 (h0.length - 1) e1.1 Ps

/-- `ComposedText.termText`, iteratively: a backtick for application. -/
def termText (t : Term) : String := Id.run do
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

/-- The prefix form parsed, iteratively (right to left, a stack of terms). -/
def parseTerm (s : String) : Except String Term := do
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
    | c => throw s!"bad term character {repr c}"
  match stack with
  | [t] => pure t
  | [] => throw "empty term"
  | _ => throw "trailing operands"

/-- `ComposedText.cellText`. -/
def cellText : Cell → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .nil => "N"
  | .app f x => s!"A {f} {x}"
  | .cons x r => s!"C {x} {r}"
  | .atom n => s!"X {n}"

/-- `ComposedText.defaultLog`: the heights a statement need not name. -/
def defaultLog : Nat × Nat := (11, 11)

/-- `ComposedText.logOK`: each log height in `[9, 20]`. -/
def logOK (lg : Nat × Nat) : Bool := 9 ≤ lg.1 && lg.1 ≤ 20 && 9 ≤ lg.2 && lg.2 ≤ 20

/-- `ComposedText.privateOK` for a predicate: the bits and the region fill
    at most `2^8` private cells. -/
def privateOK (n W : Nat) : Bool := 0 < W && n + W ≤ 2 ^ 8

/-- The region's size: one cell, since the predicate reads no witness
    (`SkilarkZK.W`). -/
def W : Nat := 1

/-- `ComposedText.publicTextC (.pred V x n) W lg`: the statement's text. -/
def publicText (V x : Term) (n : Nat) (lg : Nat × Nat) : String := Id.run do
  let shp := combBT n
  let N := nleaves shp
  let region := List.replicate W Cell.S
  let (heap0, roots) := cHeap (fun _ => false) shp region [predStmt V x]
  let heap := heap0 ++ [Cell.nil]
  let hd := roots.getD 0 0
  let stk := heap0.length
  let logLine := if lg == defaultLog then "" else s!"log {lg.1} {lg.2}\n"
  let mut s := s!"predicate {termText V} {termText x} {n}\nW {W}\n{logLine}bits {N}\nroots {" ".intercalate (roots.map toString)}\nnil {stk}\n{hd} {stk} {heap.length}\n"
  let mut i := 0
  for c in heap do
    s := s ++ (if 3 ≤ i && i < N + 3 + W then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- A predicate statement's header: `predicate V x n`, `W w`, and the
    heights when named. -/
structure Header where
  V : Term
  x : Term
  n : Nat
  W : Nat
  lg : Nat × Nat

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

/-- The header of a statement's text (the rest is `publicText`'s to compare). -/
def parseHeader (text : String) : Except String Header := do
  let ls := text.splitOn "\n"
  let (V, x, n) ← match words (ls.getD 0 "") with
    | ["predicate", v, x, n] =>
      let some n := n.toNat? | throw "the bit count is not a number"
      if n = 0 then throw "a predicate over no bits"
      pure (← parseTerm v, ← parseTerm x, n)
    | _ => throw "the first line is not `predicate V x n`"
  let W ← match words (ls.getD 1 "") with
    | ["W", w] => match w.toNat? with
      | some w => pure w
      | none => throw "the region size is not a number"
    | _ => throw "the second line is not `W n`"
  let lg ← match words (ls.getD 2 "") with
    | ["log", r, m] => match r.toNat?, m.toNat? with
      | some r, some m => pure (r, m)
      | _, _ => throw "the heights are not numbers"
    | ["log", _, _, _, _] => throw "a statement for the circuit with jets"
    | _ => pure defaultLog
  return ⟨V, x, n, W, lg⟩

/-- The witness file: one line per bit, then the region's cells
    (`SkilarkZK.witnessText`). -/
def witnessText (bits : List Bool) (region : List Cell) : String :=
  bits.foldl (fun s b => s ++ (if b then "1" else "0") ++ "\n") "" ++
    region.foldl (fun s c => s ++ cellText c ++ "\n") ""

end Nock2Ski.PredText
