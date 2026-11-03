import Nock2Ski.InterpPins

open Nock
open Term
open Compose (boolT)
open BitArith (bl nilT consT consO ttO ffO wnf run)

set_option linter.unusedSimpArgs false

/-!
# The pins of the equations

The second half of `InterpPins.lean`: `x_pin` for every equation of the
interpreter, `op12` and `app`.
-/

namespace Nock2Ski

theorem decop11_pin : Front.termOf nockFile (nm! "decop11") = some decop11T := termD_pin (by decide +kernel)
theorem decop01_pin : Front.termOf nockFile (nm! "decop01") = some decop01T := termD_pin (by decide +kernel)
theorem decop10_pin : Front.termOf nockFile (nm! "decop10") = some decop10T := termD_pin (by decide +kernel)
theorem decop00_pin : Front.termOf nockFile (nm! "decop00") = some decop00T := termD_pin (by decide +kernel)
theorem revb_pin : Front.termOf nockFile (nm! "revb") = some revbT := termD_pin (by decide +kernel)
theorem tlb_pin : Front.termOf nockFile (nm! "tlb") = some tlbT := termD_pin (by decide +kernel)
theorem path_pin : Front.termOf nockFile (nm! "path") = some pathT := termD_pin (by decide +kernel)
theorem descend_pin : Front.termOf nockFile (nm! "descend") = some descendT := termD_pin (by decide +kernel)
theorem slotB_pin : Front.termOf nockFile (nm! "slotB") = some slotBT := termD_pin (by decide +kernel)
theorem editP_pin : Front.termOf nockFile (nm! "editP") = some editPT := termD_pin (by decide +kernel)
theorem editB_pin : Front.termOf nockFile (nm! "editB") = some editBT := termD_pin (by decide +kernel)
theorem autocons_pin : Front.termOf nockFile (nm! "autocons") = some autoconsT := termD_pin (by decide +kernel)
theorem appI_pin : Front.termOf nockFile (nm! "appI") = some appIT := termD_pin (by decide +kernel)
theorem cel2_pin : Front.termOf nockFile (nm! "cel2") = some cel2T := termD_pin (by decide +kernel)
theorem op12_pin : Front.termOf nockFile (nm! "op12") = some op12T := termD_pin (by decide +kernel)
theorem decop1_pin : Front.termOf nockFile (nm! "decop1") = some decop1T := termD_pin (by decide +kernel)
theorem decop0_pin : Front.termOf nockFile (nm! "decop0") = some decop0T := termD_pin (by decide +kernel)
theorem nockO_pin : Front.termOf nockFile (nm! "nockO") = some nockOT := termD_pin (by decide +kernel)
theorem decop_pin : Front.termOf nockFile (nm! "decop") = some decopT := termD_pin (by decide +kernel)
theorem nockP_pin : Front.termOf nockFile (nm! "nockP") = some nockPT := termD_pin (by decide +kernel)
theorem nockI_pin : Front.termOf nockFile (nm! "nockI") = some nockIT := termD_pin (by decide +kernel)
theorem app_pin : Front.termOf nockFile (nm! "app") = some appT := termD_pin (by decide +kernel)

end Nock2Ski
