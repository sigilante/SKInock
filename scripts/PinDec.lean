import Nock2Ski.JetTransport
import Nock2Ski.HoonDec
import Std.Data.HashMap
open Term

/-- Avon's dag form: every distinct subterm once, `id=l.r`, leaves S K I, the root last. -/
structure DagSt where
  ids : Std.HashMap (Nat × Nat × Nat) Nat := {}
  lines : Array String := #[]

partial def dagOf (t : Term) : StateM DagSt Nat := do
  let key ← match t with
    | .app f x => do let a ← dagOf f; let b ← dagOf x; pure (3, a, b)
    | .S => pure (0, 0, 0) | .K => pure (1, 0, 0) | .I => pure (2, 0, 0)
  let st ← get
  match st.ids.get? key with
  | some i => pure i
  | none =>
    let i := st.ids.size
    let rhs := match key with
      | (0, _, _) => "S" | (1, _, _) => "K" | (2, _, _) => "I" | (_, a, b) => s!"{a}.{b}"
    set ({ ids := st.ids.insert key i, lines := st.lines.push s!"{i}={rhs}" } : DagSt)
    pure i

def dagText (t : Term) : String :=
  let (root, st) := (dagOf t).run {}
  "dag " ++ String.intercalate " " st.lines.toList ++ s!" @{root}"

partial def enc : Term → String
  | .S => "S" | .K => "K" | .I => "I"
  | .app f a => "`" ++ enc f ++ enc a

def size : Term → Nat
  | .app f a => size f + size a
  | _ => 1

def main : IO Unit := do
  let t := Nock2Ski.jetT Nock2Ski.decF
  IO.FS.writeFile "/Users/neal/Code/ski/skinock/terms/jetT-decF.dag" (dagText t ++ "\n")
  IO.FS.writeFile "/Users/neal/Code/ski/skinock/terms/jetT-decF.prefix" (enc t ++ "\n")
  IO.FS.writeFile "/Users/neal/Code/ski/skinock/terms/toCellT.dag" (dagText Nock2Ski.toCellT ++ "\n")
  IO.println s!"jetT decF: {size t} atoms; toCellT: {size Nock2Ski.toCellT} atoms; nockToSki decF: {size (Nock2Ski.nockToSki Nock2Ski.decF)} atoms"
  -- Hoon's `++dec`: the arm under the `%fast` hint (`hoon_dec_transport`)
  let h := Nock2Ski.jetT Nock2Ski.hoonDecBodyF
  IO.FS.writeFile "/Users/neal/Code/ski/skinock/terms/jetT-hoonDecBodyF.dag" (dagText h ++ "\n")
  IO.FS.writeFile "/Users/neal/Code/ski/skinock/terms/jetT-hoonDecBodyF.prefix" (enc h ++ "\n")
  IO.println s!"jetT hoonDecBodyF: {size h} atoms; nockToSki hoonDecBodyF: {size (Nock2Ski.nockToSki Nock2Ski.hoonDecBodyF)} atoms"
