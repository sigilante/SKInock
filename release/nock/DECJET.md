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
