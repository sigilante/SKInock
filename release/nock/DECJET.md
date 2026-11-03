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
carries code in its battery and context. Under `Enc`, the core `[bat [n ctx]]` and the inner
cell `[n ctx]` (with `n ≤ 11` read as an opcode) may each be a `Form` too. The jet must fire
on all of these. `Nock2Ski/HoonDecFree.lean` proves it does. Notation: `⟨m⟩ = encNoun (atom m)`,
and `CellLike x h t` means `x` is `cellT h t` or `formT h t k` for some `k`.

    hoon_dec_enc          : Enc s es → HoonDecDom s → jetT hoonDecBodyF ⬝ es ↠ encOut (hoonDecC s)
    hoon_dec_free_cl      : CellLike s B X → CellLike X ⟨n+1⟩ C → jetT hoonDecBodyF ⬝ s ↠ ⟨n⟩
    hoon_dec_free_cl_zero : CellLike s B X → CellLike X ⟨0⟩ C   → jetT hoonDecBodyF ⬝ s ↠ Err
    hoon_dec_err_atom b   : jetT hoonDecBodyF ⬝ atomT b ↠ Err                  (any bit term b)
    hoon_dec_err_noSample : CellLike s B (atomT b) → jetT hoonDecBodyF ⬝ s ↠ Err  (any b)
    hoon_dec_fire_sound   : hoonDecFire? t = some u → jetT hoonDecBodyF ⬝ t ↠ u

`B`, `C` and the codes `k` are **any** closed terms, with no `Enc` hypothesis, even divergent
ones. The compiled arm never applies, projects into or forces them. It copies the subject
into the loop core `[loop [i S]]` and reads only axis 6 of `S` (the sample) and its own
counter. On those projections a `Form` behaves exactly as a `Cell` (`hd_form`, `tl_form`,
`force_form`). The sample must be a canonical atom, because `eqT` compares bit lists. The
atom in the two `Err` shapes may have any bit term, because the arm only checks that it is
not a cell.

**The fire check, for a C implementer** (`hoonDecFire?`). Match on literal constructors:

- `CELL(h, t)` is `K (S (K K) (S (K K) (S (S I (K h)) (K t))))`, i.e. `cellT h t`.
- `FORM(h, t, k)` is `K (K (S (K K) (S (S (S I (K h)) (K t)) (K k))))`, i.e. `formT h t k`
  (`Nock2Ski/Noun.lean`: `K ⬝ (K ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ pairT h t ⬝ (K ⬝ k))))`, with
  `pairT h t = S (S I (K h)) (K t)`).
- `ATOM(b)` is `S (K K) (S (K K) (S (K K) (S I (K b))))`, i.e. `atomT b`.
- `PAIR(h, t)` means `CELL(h, t)` or `FORM(h, t, k)` for any `k`. Never inspect `k`.

Given the input term `t`:

1. **Fire `Err`** (output `K (K (K I))`) if `t` is `ATOM(b)` for any `b`, or if `t` is
   `PAIR(B, x)` with `x` an `ATOM(b)` for any `b`. `B` and `b` are not inspected.
   (`HoonDecErrFires`, `hoon_dec_err_fires`.)
2. **Fire with a value** if `t` is `PAIR(B, x)`, `x` is `PAIR(a, C)`, `a` is `ATOM(bits)`, and
   all of the following hold. `B` and `C` are not inspected.
   - `bits` is a bit list, least significant first: `K` is nil, and `K (S (S I (K h)) (K
     rest))` is a cons with `h` literally `K` (bit 1) or `K I` (bit 0).
   - The list is canonical: empty, or its last bit is 1.
   - Its value is `m < 2^32`.

   The output is `atomT (bl (bits (m-1)))` (canonical) when `m ≥ 1`, and `K (K (K I))`
   (`Err`) when `m = 0`. (`HoonDecFires`, `hoon_dec_fires_sound`.)
3. **Decline** otherwise, and the term runs. That covers a cell or `Form` sample (the term
   diverges there, so declining is the only correct answer), a non-canonical sample atom,
   `m ≥ 2^32`, and any term that is not literally one of these shapes.

The shapes in 1 and 2 are disjoint. `hoonDecFire?` checks 1 first, but the order does not
matter. A term that only reduces to a cell is not matched, so a check over a shared graph
must match the tree that the graph denotes. `hoonDecFires_pins` pins every case by kernel
evaluation: both cells `Form`s, an atom core with non-canonical bits, `[B atom]` under a
`Form`, and the declines.

Measurement (the Hoon `++dec` benchmark, fired against unfired on Avon) is pending zori's
jet for this term.
