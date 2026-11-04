import Nock2Ski.DecNorm
import Nock2Ski.DecTermNock
import Nock2Ski.DecLoop

/-!
# nocknorm: the Λ loop with the normalised `dec` jet, on the write-once machine

`lake exe nocknorm run N...` runs, for each loop length `N`, the check of
the Nock claim `*[[N [0 0]] decLoopF] = [0 [0 0]]` (`checkT`, M4c's `eqn`
of the compiled loop on `encNoun [N [0 0]]` against `encNoun [0 [0 0]]`)
on lean-ski's heap machine (`Ski/Heap.lean`, `mstep`, cell for cell):

- **unjetted**: the check as it is, the compiled word `dec` in place;
- **bare jet**: every occurrence of the compiled word replaced by the jet's
  atom `JD`, the jet's row `DecJet.decRowI` firing on the machine's
  memory (the reader through `K`-thunks); the run stops at the first call,
  whose argument is not laid out;
- **normalised jet**: every occurrence replaced by `normJ JD = S normT (K
  JD)` (`Nock2Ski/DecNorm.lean`): the normaliser runs on the machine and
  hands the jet its argument, which `DecJet.decRowI` reads and decrements,
  writing `outCells` at the counter.

It prints the machine's transitions (the CPU's rows), its contractions, the
jet's calls, the cells written, and whether the run reaches `K`.  The jet's
row is the Lean function `DecJet.decRowI`'s reader and writer
(`readSubjI`, `headFits`, `outCells`) on the memory as a list.
-/

open Nock Nock2Ski Term Mach

namespace NockNorm

/-- Replace every occurrence of `P` in `t` by `D`. -/
def replaceO (P : _root_.Term) (D : OTerm) : _root_.Term → OTerm
  | .S => if _root_.Term.S = P then D else .S
  | .K => if _root_.Term.K = P then D else .K
  | .I => if _root_.Term.I = P then D else .I
  | .app f x => if _root_.Term.app f x = P then D else .app (replaceO P D f) (replaceO P D x)

structure St where
  heap : Array Cell
  hd : Nat
  stk : Nat

/-- Load a term as a tree of cells, iteratively. -/
def load (heap : Array Cell) (t : OTerm) : Array Cell × Nat := Id.run do
  let mut h := heap
  let mut todo : List (OTerm × Bool) := [(t, false)]
  let mut out : List Nat := []
  repeat
    match todo with
    | [] => break
    | (u, done) :: rest =>
      todo := rest
      match u with
      | .app f x =>
        if done then
          match out with
          | xa :: fa :: o => h := h.push (.app fa xa); out := (h.size - 1) :: o
          | _ => pure ()
        else todo := (f, false) :: (x, false) :: (u, true) :: todo
      | .S => h := h.push .S; out := (h.size - 1) :: out
      | .K => h := h.push .K; out := (h.size - 1) :: out
      | .I => h := h.push .I; out := (h.size - 1) :: out
      | .var j => h := h.push (.atom j); out := (h.size - 1) :: out
  -- `f` is pushed before `x`, so the pending order is reversed
  return (h, out.headD 0)

def get (h : Array Cell) (a : Nat) : Option Cell := h[a]?

structure Res where
  rows : Nat
  contractions : Nat
  jets : Nat
  written : Nat
  verdict : String

/-- Run the machine, the jet `J` firing through `DecJet.decRowI`'s reader. -/
def run (s0 : St) (J : Nat) (fuel : Nat) : Res := Id.run do
  let base := s0.heap.size
  let mut s := s0
  let mut rows := 0
  let mut nc := 0
  let mut jets := 0
  for _ in [0:fuel] do
    match get s.heap s.hd with
    | some (.app f x) =>
      let h := s.heap.push (.cons x s.stk)
      s := ⟨h, f, h.size - 1⟩; rows := rows + 1
    | some .I =>
      match get s.heap s.stk with
      | some (.cons x r) => s := ⟨s.heap, x, r⟩; rows := rows + 1; nc := nc + 1
      | _ => return ⟨rows, nc, jets, s.heap.size - base, "whnf I"⟩
    | some .K =>
      match get s.heap s.stk with
      | some (.cons x s1) =>
        match get s.heap s1 with
        | some (.cons _ s2) => s := ⟨s.heap, x, s2⟩; rows := rows + 1; nc := nc + 1
        | _ =>
          return ⟨rows, nc, jets, s.heap.size - base, if (get s.heap s1) == some .nil then "K x" else "whnf K"⟩
      | _ =>
        return ⟨rows, nc, jets, s.heap.size - base, if (get s.heap s.stk) == some .nil then "K" else "whnf K"⟩
    | some .S =>
      match get s.heap s.stk with
      | some (.cons x s1) =>
        match get s.heap s1 with
        | some (.cons y s2) =>
          match get s.heap s2 with
          | some (.cons z s3) =>
            let h1 := s.heap.push (.app y z)
            let h2 := h1.push (.cons (h1.size - 1) s3)
            let h3 := h2.push (.cons z (h2.size - 1))
            s := ⟨h3, x, h3.size - 1⟩; rows := rows + 1; nc := nc + 1
          | _ => return ⟨rows, nc, jets, s.heap.size - base, "whnf S"⟩
        | _ => return ⟨rows, nc, jets, s.heap.size - base, "whnf S"⟩
      | _ => return ⟨rows, nc, jets, s.heap.size - base, "whnf S"⟩
    | some (.atom j) =>
      if j != J then return ⟨rows, nc, jets, s.heap.size - base, "whnf atom"⟩
      match get s.heap s.stk with
      | some (.cons p rest) =>
        let H := s.heap.toList
        match DecJet.readSubjI H H.length p with
        | some (sj, csk, ask, sks) =>
          if DecJet.headFits sj then
            match DecJet.outCells H.length sj csk ask sks with
            | some (cells, root) =>
              s := ⟨s.heap ++ cells.toArray, root, rest⟩; rows := rows + 1; jets := jets + 1
            | none => return ⟨rows, nc, jets, s.heap.size - base, s!"STOPPED at call {jets + 1}: no output"⟩
          else return ⟨rows, nc, jets, s.heap.size - base, s!"STOPPED at call {jets + 1}: the head does not fit"⟩
        | none =>
          return ⟨rows, nc, jets, s.heap.size - base,
            s!"STOPPED at call {jets + 1}: the argument is not readable by DecJet.readSubjI"⟩
      | _ => return ⟨rows, nc, jets, s.heap.size - base, "whnf J"⟩
    | _ => return ⟨rows, nc, jets, s.heap.size - base, "stuck"⟩
  return ⟨rows, nc, jets, s.heap.size - base, "out of fuel"⟩

/-- The slots `K`, `I`, `K I` at 0, 1, 2 (`DecJet.slotsOK`), then the term,
    then the empty stack. -/
def start (t : OTerm) : St :=
  let h0 : Array Cell := #[.K, .I, .app 0 1]
  let (h1, root) := load h0 t
  let h2 := h1.push .nil
  ⟨h2, root, h2.size - 1⟩

def loopS (n : Nat) : Noun := .cell (.atom n) (.cell (.atom 0) (.atom 0))
def loopP : Noun := .cell (.atom 0) (.cell (.atom 0) (.atom 0))

def J : Nat := ComposedDText.JD

def report (name : String) (r : Res) : String :=
  s!"{name}: {r.rows} rows, {r.contractions} contractions, {r.jets} jet calls, {r.written} cells written, {r.verdict}"

def main (args : List String) : IO UInt32 := do
  match args with
  | "run" :: ns =>
    for a in ns do
      let n := a.toNat!
      let c := checkT decLoopF (loopS n) loopP
      let fuel := 1 <<< 30
      IO.println (report s!"loop_{n} unjetted      " (run (start c.toO) J fuel))
      IO.println (report s!"loop_{n} bare jet      " (run (start (replaceO (nockToSki decF) (.var J) c)) J fuel))
      IO.println (report s!"loop_{n} normalised jet"
        (run (start (replaceO (nockToSki decF) (.S ⬝ₒ DecNorm.normT.toO ⬝ₒ (.K ⬝ₒ .var J)) c)) J fuel))
    pure 0
  | _ => IO.eprintln "usage: nocknorm run N..."; pure 2

end NockNorm

def main (args : List String) : IO UInt32 := NockNorm.main args
