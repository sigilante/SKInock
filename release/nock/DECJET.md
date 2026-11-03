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

### Real cores, and the fire check

`hoon_dec_transport` is over `encNoun` inputs, which contain no `Form`. A real gate core
carries code in its battery and context, so the jet must fire there too.
`Nock2Ski/HoonDecFree.lean` proves it does. Write `⟨m⟩` for `encNoun (atom m)`:

    hoon_dec_enc       : Enc s es → HoonDecDom s → jetT hoonDecBodyF ⬝ es ↠ encOut (hoonDecC s)
    hoon_dec_free      : ∀ B C n, jetT hoonDecBodyF ⬝ cellT B (cellT ⟨n+1⟩ C) ↠ ⟨n⟩
    hoon_dec_free_zero : ∀ B C,   jetT hoonDecBodyF ⬝ cellT B (cellT ⟨0⟩ C)   ↠ Err
    hoon_dec_fires_sound : hoonDecSample? t = some m → jetT hoonDecBodyF ⬝ t ↠ encOut (hoonDecOutN m)

`B` and `C` are **any** closed terms, with no `Enc` hypothesis, even divergent ones. The
compiled arm never applies, projects into or forces them. It copies the subject into the
loop core `[loop [i S]]` and reads only axis 6 of `S` (the sample) and its own counter. The
fire check, for a C implementer, given the input term `t`:

1. `t` is literally the `Cell` value `K (S (K K) (S (K K) (S (S I (K B)) (K X))))`, i.e.
   `cellT B X`. `B` is not inspected.
2. `X` is literally `cellT a C`. `C` is not inspected.
3. `a` is literally `atomT b = S (K K) (S (K K) (S (K K) (S I (K b))))`.
4. `b` is a bit list `bl bs`: `K` is nil, and `K (S (S I (K h)) (K rest))` is a cons, with `h`
   literally `K` (bit 1) or `K I` (bit 0), least significant first.
5. `bs` is canonical: empty, or its last bit is 1. Let `m` be its value, and require
   `m < 2^32`.

If all five hold, the jet replaces the term with `⟨m-1⟩` (`atomT (bl (bits (m-1)))`) when
`m ≥ 1`, and with `Err` (`K (K (K I))`) when `m = 0`. Otherwise it declines, and the term
runs. This is `HoonDecFires t` (`hoonDecSample? t = some m ∧ m < 2^32`), and
`hoon_dec_fires` proves that the replacement is the term's own reduct. A cell sample, a
`Form` sample or a non-canonical atom declines (`hoonDecFires_pins`). On a cell sample the
term diverges, so declining is the only correct answer. On `cellT B ⟨t⟩` (no axis 6) the
term reaches `Err` too (`hoon_dec_free_noSample`), but the check declines and lets it run.
Shapes are syntactic: the check matches the term's constructors exactly, and a term that
only reduces to a cell is not matched. A check over a shared graph must therefore match the
tree that the graph denotes.

Measurement (the Hoon `++dec` benchmark, fired against unfired on Avon) is pending zori's
jet for this term.
