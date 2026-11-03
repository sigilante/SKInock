import Nock2Ski.InterpEqI

open Nock
open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

set_option linter.unusedSimpArgs false

/-!
# The pins: every name's term is the file's

`x_pin : Front.termOf nockFile (nm! "x") = some xT` for every constructor
of `op` and every equation of the interpreter, `op12` and `app`.  Each is
`termD_pin` (`Decls.lean`) on the kernel's check that the file defines the
name; the terms were pinned to Python's output character for character
(`scripts/lean-check.sh` does not re-check this; `Front` is the reference).
-/

namespace Nock2Ski

theorem O0_pin : Front.termOf nockFile (nm! "O0") = some (opC 0) := by
  rw [nockFile_eq]; decide +kernel
theorem O1_pin : Front.termOf nockFile (nm! "O1") = some (opC 1) := by
  rw [nockFile_eq]; decide +kernel
theorem O2_pin : Front.termOf nockFile (nm! "O2") = some (opC 2) := by
  rw [nockFile_eq]; decide +kernel
theorem O3_pin : Front.termOf nockFile (nm! "O3") = some (opC 3) := by
  rw [nockFile_eq]; decide +kernel
theorem O4_pin : Front.termOf nockFile (nm! "O4") = some (opC 4) := by
  rw [nockFile_eq]; decide +kernel
theorem O5_pin : Front.termOf nockFile (nm! "O5") = some (opC 5) := by
  rw [nockFile_eq]; decide +kernel
theorem O6_pin : Front.termOf nockFile (nm! "O6") = some (opC 6) := by
  rw [nockFile_eq]; decide +kernel
theorem O7_pin : Front.termOf nockFile (nm! "O7") = some (opC 7) := by
  rw [nockFile_eq]; decide +kernel
theorem O8_pin : Front.termOf nockFile (nm! "O8") = some (opC 8) := by
  rw [nockFile_eq]; decide +kernel
theorem O9_pin : Front.termOf nockFile (nm! "O9") = some (opC 9) := by
  rw [nockFile_eq]; decide +kernel
theorem O10_pin : Front.termOf nockFile (nm! "O10") = some (opC 10) := by
  rw [nockFile_eq]; decide +kernel
theorem O11_pin : Front.termOf nockFile (nm! "O11") = some (opC 11) := by
  rw [nockFile_eq]; decide +kernel
theorem O12_pin : Front.termOf nockFile (nm! "O12") = some (opC 12) := by
  rw [nockFile_eq]; decide +kernel
theorem Obad_pin : Front.termOf nockFile (nm! "Obad") = some (opC 13) := by
  rw [nockFile_eq]; decide +kernel

end Nock2Ski
