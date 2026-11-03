# The `dec` jet on Avon (2026-11-04)

Avon master 72e5254 (PR #121) carries a native `dec` licensed against `jetT decF`
(`terms/jetT-decF.dag`, digest 17bcbb92…, Lean's own term via `scripts/PinDec.lean`),
the implementation `dec_transport : Implements (nounContract decC) (jetT decF)` proves.
It fires only on `encNoun` of a stack with a canonical head of at most 32 bits; anything
else declines and the term runs. Inputs from `scripts/decgen.py` (zori's generator).

`avon reduce` share mode, unjetted vs `--nock-dec`, normal forms compared byte for byte:

| stack | unjetted | jetted | normal forms |
|---|--:|--:|---|
| `[7 0]` | 9,528 | 1 | equal |
| `[100 [3 4]]` | 134,422 | 1 | equal |
| `[10000 0]` | 13,430,171 | 1 | equal |
| `[1000000 0]` | 1,343,017,090 | 1 | equal |
| `[0 0]` (underflow) | 577 | 1 | equal (`Err`) |
| `[[1 2] 0]` (cell head) | 242 | 1 | equal (`Err`) |

The unjetted cost is the count-up loop, about 1,343 contractions per unit of the
argument; the jet makes it one step. The circuit side is lean-ski branch `dec-jet`
(`release/dec` there); its export-soundness theorem is in progress.

## Hoon's own `++dec` (2026-11-04)

`terms/jetT-hoonDecBodyF.dag` (and `.prefix`) is `jetT hoonDecBodyF`, written by
`scripts/PinDec.lean` from Lean's own term: 65,093 atoms; `nockToSki hoonDecBodyF` is 64,918.
sha256 of the dag file: `929d398137d65283b50f941877177a4472adeaffe02543483aca784ec9612503`.
`Nock2Ski/HoonDec.lean` proves its contract:

    hoon_dec_transport : Implements (onContract HoonDecDom hoonDecC) (jetT hoonDecBodyF)

- **Input**: `encNoun` of the gate core `[bat [sam ctx]]`, with the sample at axis 6. The
  battery slot is not read. The domain `HoonDecDom` is every noun except a core whose sample
  is a cell, where Hoon's `++dec` diverges (`hoon_dec_off_domain`). A jet must decline there.
- **Output**: `encNoun (atom n)` on `[bat [n+1 ctx]]`, code-free through `toCell`. `Err` on
  `[bat [0 ctx]]`, on an atom, and on `[bat atom]`.
- **Matched term**: the compiled body, not the hinted battery. The benchmark's `dec.nock`
  gate has no hint. The released programs and lean-nock's `decBat` put the body under a `~_`
  (`%mean`) hint. Neither has a `%fast` hint: `hoon.hoon`'s `~/ %dec` (`~% %dec +7 ~`) wraps
  the gate's construction.
- **Registration** (metadata, not part of the licence): name `%dec`, parent axis 7, no hooks.

Measurement (the Hoon `++dec` benchmark, fired against unfired on Avon) is pending zori's
jet for this term.
