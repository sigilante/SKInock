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

Measurement of the term applied directly to a core is in the next section.

## In whole programs (2026-11-04)

Avon master 7dc994b runs `jetT hoonDecBodyF` natively (kind `hoon-dec` in `--pins`). It
fires when the term is applied directly to a core. It has never fired inside a whole
compiled program, for three separate reasons.

**1. A program does not contain the licensed term.** `jetT f = S (K toCellT) (nockToSki f)`
exists only as a pinning device. A compiled program contains the **bare arm**
`nockToSki hoonDecBodyF`. It appears as the code field of the body's `Form` (`encLit` of the
battery) and inside the compiled hint `force (H s) (K (C s))`. The arm's outputs on the fire
shapes, `encNoun (atom n)` and `errT`, contain no `Form`, so `toCell` is the identity on them
and the same family holds for the bare arm, with the same fire check
(`Nock2Ski/HoonDecFree.lean`):

    hoon_dec_bare_enc          : Enc s es → HoonDecDom s → nockToSki hoonDecBodyF ⬝ es ↠ encOut (hoonDecC s)
    hoon_dec_bare_cl           : CellLike s B X → CellLike X ⟨n+1⟩ C → nockToSki hoonDecBodyF ⬝ s ↠ ⟨n⟩
    hoon_dec_bare_cl_zero      : CellLike s B X → CellLike X ⟨0⟩ C   → nockToSki hoonDecBodyF ⬝ s ↠ Err
    hoon_dec_bare_err_atom b   :                                      nockToSki hoonDecBodyF ⬝ atomT b ↠ Err
    hoon_dec_bare_err_noSample : CellLike s B (atomT b)             → nockToSki hoonDecBodyF ⬝ s ↠ Err
    hoon_dec_bare_fire_sound   : hoonDecFire? t = some u → nockToSki hoonDecBodyF ⬝ t ↠ u
    hoon_dec_bare_fire_sound_red : t ↠ t' → hoonDecFire? t' = some u → nockToSki hoonDecBodyF ⬝ t ↠ u
    hoon_dec_fire_sound_red      : t ↠ t' → hoonDecFire? t' = some u → jetT hoonDecBodyF ⬝ t ↠ u

`hoon_dec_bare_enc` uses the fact that the only encoding of an atom is `encNoun`
(`Enc.atom_inv`). The others are the pre-`toCell` lemmas of the `jetT` family
(`hoon_dec_body_cl`, `hoon_dec_body_cl_zero`, `dec_body_err`), restated. All of them use
`propext`, `Classical.choice` and `Quot.sound`, as the `jetT` family does.

`terms/nockToSki-hoonDecBodyF.dag` (and `.prefix`), written by `scripts/PinDec.lean`, is
the bare term: 64,918 atoms and 1,386 DAG nodes. sha256 of the dag file is
`875515052b4f4eaada5a91cd71e2ebc49851571786bd5b27982806550dd1b3cf`. Avon's full digest
(`av_pin_digest`) is `d320b173f4b5afcad727a12dde7857b9b698acfc45fea1f6c353d8e87b14a54f`.
`jetT hoonDecBodyF`'s digest is `a4baf0aa…`. Kind `hoon-dec` is tied to that one digest
(`av_hoon_dec_register`), so Avon refuses the bare term until it accepts a second digest.

**Where the arm occurs.** The program is `hoon_dec_N`: release/nock/programs.txt's
`hoon_dec_12` formula with the sample `[1 N]`, at subject 0. Its shared form at N = 12 is
byte-identical to the corpus row.

| form | atoms | literal occurrences of `nockToSki hoonDecBodyF` |
|---|--:|--:|
| unshared, `compiled f 0` (`--unshared`) | 1,077,188 (N = 7) | 3 as tree subterms (1 as a `Form`'s code field). Hash-consed (DAG input), they are 1 node |
| shared, `share (compiled f 0)` (the corpus row) | 30,100 (N = 7) | **0** |

`share` replaces the repeated subterms inside the arm with variables, so the shared row
does not contain the arm literally. Its β-reduct does (`share_red : share t ↠ t`), but Avon
binds pinned terms once, at load (`av_pin_bind`), and never in a reduct. A program that
should fire therefore has to be loaded unshared, as a DAG.

**2. Avon does not bind a pinned term in a prefix-form input.** Loaded as a backtick-prefix
tree, even the direct application `jetT hoonDecBodyF ⬝ core` reports "no pinned term occurs".
The DAG form of the same term binds. The likely cause is `pin_same`'s equality budget of
`8 · pin_nodes + 4096`, which is 15,376 for `jetT` (1,410 DAG nodes). A tree-loaded copy is
not hash-consed and has about 130,000 nodes to compare, so `av_pin_bind` unbinds it. For that
reason every measurement below uses DAG input (Lean's `dagText`, as in `PinDec.lean`). The DAG
input also changes the unjetted counts slightly: 12,295 against 12,484 for the prefix form at
N = 7.

**3. At the call the argument is not a core "as it stands".** With the bare term bound (a
private Avon build that only adds the second digest), the arm is bound once, called once, and
**declined** at every N. It is applied lazily to an unreduced core. The argument is the redex
`K (I (K Z)) W`, which reduces to `K Z = cellT bat tl` in two steps. Inside it, the field
`K tl` is itself the redex `(K K) (K (K Q)) R`, and the sample's cell and bits are further
redexes. The literal fire check (`av_hoon_dec_read`, `hoonDecFire?`) cannot match it. Reducing
the argument first is sound by `hoon_dec_bare_fire_sound_red`, because Avon's in-place steps
are weak reductions `t ↠ t'`. The arm forces exactly these parts anyway: the core, its tail,
and the sample with its bit list.

**Numbers.** Avon `reduce`, share mode, `--budget=10^11`, normal forms compared byte for byte.
`unjetted` and `jetT pins` are Avon 7dc994b, the latter with `--pins` listing
`hoon-dec jetT-hoonDecBodyF.dag`. `bare pins` is the private build with
`hoon-dec nockToSki-hoonDecBodyF.dag`.

The whole program `hoon_dec_N`, unshared, as a DAG:

| N | unjetted | jetT pins | bare pins | normal forms |
|--:|--:|--:|--:|---|
| 7 | 12,295 | 12,295 (no occurrence) | 12,295 (1 bound, 0 fired, 1 declined) | equal |
| 100 | 170,640 | 170,640 (no occurrence) | 170,640 (1 bound, 0 fired, 1 declined) | equal |
| 10,000 | 17,040,411 (0.30 s, 58 MB) | 17,040,411 (no occurrence) | 17,040,411 (declined) | equal |
| 100,000 | 170,406,486 (3.1 s, 453 MB) | n/a | n/a | n/a |

N = 1,000,000 unjetted would take about 1.7·10^9 steps and around 4.5 GB, past this
machine's budget while the Lean builds run. Jetted it is the same run, since the jet declines.

For the record, the direct application, the term applied to `encNoun [0 [N [0 0]]]`:

| N | `jetT ⬝ core` unjetted | jetted (7dc994b) | `nockToSki ⬝ core` unjetted | jetted (bare pin) | normal forms |
|--:|--:|--:|--:|--:|---|
| 7 | 11,331 | 1 | 11,286 | 1 | equal |
| 100 | 169,676 | 1 | 169,631 | 1 | equal |
| 10,000 | 17,039,447 (0.31 s) | 1 | 17,039,402 | 1 | equal |
| 100,000 | 170,405,522 (3.1 s, 502 MB) | 1 | 170,405,477 | 1 | equal |
| 1,000,000 | not run | 1 | not run | 1 | (unjetted not run) |

At N = 7 and 100 the `jetT` numbers are zori's (`[0 [7 [0 0]]]` 11,331 → 1). With only the
bare pin, `jetT ⬝ core` fires after 46 steps, because its bare subterm is reached through the
`S (K toCellT)` wrapper.

**What the jet needs in order to fire in a whole program:**

1. Avon accepts `nockToSki hoonDecBodyF` as a second pinned term of kind `hoon-dec`.
   `av_hoon_dec_read` and `hoon_dec_build` stay as they are.
2. `av_pin_bind` binds tree-loaded inputs, or programs are passed as DAGs.
3. Before the read, `av_hoon_dec_read` reduces the argument in place, under a budget, to the
   fire shape: the core to `K (S (K K) (S (K K) (S (S I (K bat)) (K tl))))`, `tl` likewise,
   and the sample and its bit list. If it cannot, it declines. The licence is
   `hoon_dec_bare_fire_sound_red`.
4. The program is loaded unshared, or Avon binds pins after the sharing βs.

### Fired in whole programs: Avon branch `jet-reduce-arg` (2026-11-04)

Avon branch `jet-reduce-arg` (commit `2f0843b`, merged to Avon master as `d9e888d`, PR #123, 2026-11-06) makes the four changes listed
above:

1. Kind `hoon-dec` accepts both full digests: `jetT hoonDecBodyF` (`a4baf0aa…`) and the
   bare arm `nockToSki hoonDecBodyF` (`d320b173…`). `terms/nockToSki-hoonDecBodyF.dag` is
   vendored as `jets/pins/nockToSki-hoonDecBodyF.dag`, and `jets/pins.conf` lists both
   (`hoon-dec` is the one kind that may have two lines). `--pins` reports each term's
   occurrences, e.g. `(jetT 0, bare 1)`.
2. Before the literal check, the reader reduces the argument in place. Each node the
   check reads is first reduced to weak head normal form by a nested share-mode run of
   Avon's reducer. Those nodes are the core, its tail, the sample and the sample's bit
   list, which are what the arm forces itself; `bat`, `ctx` and a `Form`'s code are never
   forced. The reductions are capped at 2^22 contractions per call (or the fuel left).
   If the cap is reached, the jet declines and the reducts stay in the graph.
   The reductions count as contractions of the run, and the fire is one step more. The
   licence is `hoon_dec_bare_fire_sound_red` (and `hoon_dec_fire_sound_red`). The Λ word's
   reader (`nock-dec`) had the same limitation and now reduces its argument the same way,
   licensed by `dec_transport` after `WSteps.right`.
3. A term loaded as a tree now binds. `pin_same`'s comparison budget is now at least the
   pinned term's size as a tree (capped at 2^22), not only `8 · pin_nodes + 4096`. That
   was the cause: a tree copy of the arm has about 65,000 application nodes against a
   budget of 15,376. The input is not hash-consed, so its counts are unchanged.
4. Shared programs are documented as out of reach. Binding pins in reducts would mean
   hashing every node a contraction builds. So a program whose `++dec` should fire must
   be loaded unshared (as a DAG or as a prefix tree).

The whole program `hoon_dec_N`, unshared, as a DAG; Avon `reduce`, share mode,
`--budget=10^11`, `--pins` (the branch's `jets/pins.conf`) against no pins, normal forms
compared byte for byte:

| N | unjetted | jetted | arm | normal forms |
|--:|--:|--:|---|---|
| 7 | 12,295 | **1,011** | bare: 1 bound, 1 fired, 0 declined | equal (116 bytes) |
| 100 | 170,640 | **1,011** | the same | equal (220 bytes) |
| 10,000 | 17,040,411 (0.48 s, 58 MB) | **1,011** (0.04 s, 6 MB) | the same | equal (400 bytes) |

The jetted count does not depend on N. Its 1,010 steps besides the fire are the program's
own work outside the arm, including the reduction of the core. That matches the unjetted
gap between the whole program and the direct application (12,295 − 11,286 = 1,009 at
N = 7). The same program as a backtick-prefix tree now binds the arm at all three of its
tree occurrences: 12,484 / 170,938 / 17,040,897 steps unjetted, 1,011 jetted, normal forms
equal. The shared form still binds nothing (15,628 steps at N = 7, jetted or not). The
direct applications `nockToSki hoonDecBodyF ⬝ core` and `jetT hoonDecBodyF ⬝ core` fire in
one step, as DAG and as prefix. Avon's `tests/test_nockdec.c` checks `hoon_dec_7` itself
against the unjetted normal form (`tests/data/hoon-dec/`), together with lazy cores
(`K`/`I`/`S K K` thunks at the core, the tail, the sample and its bits, `Form`s, divergent
`bat`/`ctx`), lazy stacks, the bare arm and a tree copy of each term.

## Inside a loop, on the circuit: why no term can lay the argument out (2026-11-04)

On Avon the jet fires inside a loop once the argument is reduced in place before the read
(item 3 above; Avon branch `jet-reduce-arg`, 2f0843b). The circuit has no in-place step: it
runs lean-ski's write-once heap machine (`Ski/Heap.lean`, `Mach`), and the `dec` row reads
its subject from memory cell by cell (`DecJet.readNn`). The question was whether a closed
term `norm` could stand in for the missing step, `J ⬝ (norm ⬝ x)` with `norm ⬝ x` written
out as an `encNn` the row reads (route A), or whether the row itself must change (route B).
**Route A is impossible.** That is a property of the machine, not of `norm`.

**What the machine writes.** Its only application-cell write is `y z` in `S x y z ⟶ x z (y
z)`, where `y` and `z` are the stack entries below `x`, and the next head is `x`. Every
wrapper of the encoding the row reads (`atomT`'s `S (K K)` cells, `cellT`'s outer `K`, every
`K h` field slot, a bit list's `Cons`) is an application cell whose function is a constant
combinator.

**The invariant** (lean-ski `Ski/NoLayout.lean`, branch `dec-norm`, built in the umbrella,
no `sorry`). Mark the input-dependent cells with a predicate `D`. Then on every reachable
state two things hold. Along the head and the stack, top first, no input-independent entry
follows an input-dependent one (`Mono`). And no cell has an input-dependent function over an
input-independent argument (`CellsOK`).

    inv_step         : Inv D m → mstep m = some m' → ∃ D', D' agrees with D on m's cells ∧ Inv D' m'
    inv_reach        : Reach m m' → Inv D m → ∃ D', … ∧ Inv D' m'
    S_cont_const     : Inv D m → stack x :: y :: … → ¬ D y → ¬ D x
    run_S_cont_const : Inv D m → Reach m m' → (the same at every reachable state)

So the `S` that writes a constant-function cell over a computed field always continues with
constant code (`S_cont_const`). Constant code cannot be the return address of a traversal.
Everything input-dependent lies below the fresh cell, and the head is always the top entry.
So that work is reachable only after the fresh cell is dropped, run, or folded into the
*function* position of another cell. A dynamic continuation therefore receives a fresh
wrapper `R` only folded, as a thunk `K R w`. A normaliser must deliver at least one
sub-result to a dynamic continuation (the rest of the traversal), and a two-field cell
needs both fields as bare cells. So no term lays out a cell whose two fields are both
computed.

**Evidence by search** (`decloop/layout/`, recomputed by produce.sh and verify.sh as
`layout.txt`). `layout/search.c` enumerates every SKI term up to a leaf bound and runs each
on a model of `Mach`, with two opaque input pointers on the stack:

| goal | terms searched | reach it |
|---|--:|--:|
| control: constant `J` receives a fresh `K P` | up to 6 leaves | yes (5 leaves: ``` ``S`SJK ```) |
| continuation `k` receives `P` from below it | up to 10 leaves | none |
| `k` receives a fresh `K P` bare, from either order | up to 10 leaves (11 for `[k, P]`, one-off) | none |
| constant `J` receives `K P (K k)` or `S (K P) (K k)` | up to 9 leaves, J in the alphabet, both orders | none |
| `k` receives `K P` folded as `K (K P) w` | the 12-leaf term below | yes |

`layout/deliver.py` runs the 12-leaf term `S (K (S (S (K (S (K (S I)) K)) K))) K` on `[k,
P]`. It parks `k` as `K k`, brings `P` to the top, writes `K P`, parks that as `K (K P)`,
folds it over the parked `k` and runs the fold. `k` receives `K (K P) w` and never `K P`.
That is the K-thunk of the loop's diagnosis, and it is now known to be not just
what elimination hands back but the only form in which a computed cell can reach the rest
of a computation.

**Route B: the row through thunks, and a continuation-passing normaliser (2026-11-04).** The
row reads through `K R w`; a closed `norm` then exists, and the jet fires at every call of
the loop on the heap machine and on the circuit, whose DEC table now reads through the
thunks (lean-ski branch `dec-thunk`); the loop is measured jetted on the circuit, not proved
(below).

- **The row** (lean-ski `Ski/DecInd.lean`; `propext`, `Quot.sound`, in
  the audit manifest). `readInd` follows a thunk (`p` holds `f w`, `f` holds `k R`, `k` holds
  `K`) to `R`. The reader follows chains of them at every pointer of the need tree (the
  root, the head atom, a cell's halves, an atom's bit list and each tail) and one at a
  `Cell` wrapper's tail slot `K t` (`ktAt`). `decRowI` is `decRow` with that reader and the
  same output cells.

      decRowI_step    : the row reads back as J ⬝ u ⬝ R, u ↠ encNn s, s in the domain,
                        the next state as v ⬝ R, v ↠ encO (decSpec s)   (↠: K-contraction anywhere)
      HSteps.close_K  : a run of that head reduction to K, the jet closed to any implementation
                        of the unchanged contract, is a weak reduction to K   (Church–Rosser)
      decRow_decRowI  : on a subject without thunks the two rows agree

- **The normaliser** (`Nock2Ski/DecNorm.lean`). `normT x k` forces `x` with the
  continuation as an extra argument of the Scott cases, normalises a cell's halves and an
  atom's bits recursively, and builds each value by straight-line code from the top of the
  stack (`S (K n) c z ⟶ n (c z)` writes `c z`). It hands the value to the continuation below
  as `K Q k`. A cell's tail slot `K t` is folded over its head, so it reaches the wrapper as
  one thunk. That is the fold `NoLayout` forces, at the slot `ktAt` reads.

      norm_enc    : Enc s es → normT ⬝ es ⬝ k ↠ k ⬝ encNoun s      (Forms included)
      normJ_impl  : Implements decContract P → Implements decContract (S normT (K P))
      normDec_enc : Enc s es → S normT (K (nockToSki decF)) ⬝ es ↠ encOut (decC s)

- **The loop** (`bench/NockNorm.lean`, `lake exe nocknorm run 1 3 10 20`,
  `results-norm.txt`). The check of `*[[N [0 0]] decLoopF] = [0 [0 0]]` runs on lean-ski's
  heap machine cell for cell, the jet's row `DecJet.decRowI`'s reader and writer on the
  memory. With every occurrence of the word the jet's atom, the run stops at the first call:
  the reader through thunks does not read the computed stack. With every occurrence
  `normJ JD = S normT (K JD)`, the jet fires at every call and the run reaches `K`:

| N | unjetted contractions | unjetted transitions | normalised contractions | normalised transitions | jet calls |
|--:|--:|--:|--:|--:|--:|
| 1 | 8,434 | 20,757 | 7,051 | 17,348 | 1 |
| 3 | 23,459 | 57,785 | 14,139 | 34,805 | 3 |
| 10 | 136,500 | 336,681 | 39,730 | 97,843 | 10 |
| 20 | 466,653 | 1,152,824 | 77,294 | 190,465 | 20 |

- **The circuit** (lean-ski branch `dec-thunk`). DEC gains an indirection row kind (`K R w`
  through three slots; a need or a chain's step passed from the thunk to `R`) and reads the
  `Cell` row's tail slot through one thunk; the `Cons` row no longer peeks at its tail (a
  normalised list ends in `K K k`): the last `Cons` marks its step and the chain must end,
  through any thunks, at a nil that ends a list. Soundness re-proved: `CompDOK.jetRow`
  concludes `decRowI`, `decpreExport_sound` and `dectermExport_close` hold (backward chains
  through thunks end: `iterI_bound`). Completeness re-proved for the new table: the honest
  run's jet rows are `decRowI`'s and the honest DEC rows follow `readSubjI`, an indirection row
  per thunk on the need tree and the bit chains (`decProvides_exists`, `decpre_complete_log`). `Nock2Ski/DecLoopNorm.lean`: the statement `nockLoopV` (the word's occurrences
  `S X (K J)` under one shared `X = normT`; `nockdec emit-loop`, `check-loop`) and

      nockloop_close : an accepted proof → replT (nockToSki decF) (normJ (nockToSki decF))
                                             (checkT f s p) ↠ K

  On the circuit (`ski-air compd-measure`):

| N | CPU rows | DEC rows | jet calls | memory cells |
|--:|--:|--:|--:|--:|
| 1 | 17,544 | 20 | 1 | 2,351,104 |
| 3 | 35,165 | 64 | 3 | 2,372,203 |
| 10 | 98,777 | 238 | 10 | 2,448,148 |
| 20 | 192,219 | 508 | 20 | 2,559,181 |

  The memory is the statement's heap, the compiled program as a tree: a `2^22`-row memory
  table. A first form of `loop_1` (`normT` at each of the 13 occurrences, 2,360,598 cells)
  proved in 129 s and verified in 37 s, a 1.56 MB proof, at a 13.5 GB peak, past this
  machine's 4 GB budget.

  **Proved, with a shared statement heap (2026-11-06).** lean-ski master b9275ad (PR #70,
  zori) lays the public cells out hash-consed (`CompM.sharedL`, `Ski/HeapShared.lean`'s
  `obuildS`; header `dectermS`), with the dec circuit's soundness and completeness generalised
  over a layout (`Circuit.dectermSExport_sound`, `dectermSExport_close`; the tree theorems are
  instances with their statements unchanged). The loop's statement then holds about 2,300
  public cells instead of 2.33 million. skinock's `nockdec emit-loop` / `check-loop` write and
  check `dectermS`, and `nockloop_closeS` / `nockloop_soundS` are `nockloop_close` /
  `nockloop_sound` through the shared layout. Released in `decloop/` (`produce.sh loop`,
  `verify.sh` step 6, `results-loop.txt`):

| N | CPU rows | DEC rows | memory cells | heights | prove | verify | proof | peak |
|--:|--:|--:|--:|--|--:|--:|--:|--:|
| 1 | 17,544 | 20 | 23,429 | 15 15 9 | 1.8 s | 1.8 s | 1.12 MB | 0.66 GB |
| 3 | 35,165 | 64 | 44,514 | 16 16 9 | 3.5 s | 1.9 s | 1.17 MB | 0.67 GB |
| 10 | 98,777 | 238 | 120,437 | 17 17 9 | 6.8 s | 1.8 s | 1.23 MB | 1.17 GB |
| 20 | 192,219 | 508 | 231,457 | 18 18 9 | 13.5 s | 2.2 s | 1.28 MB | 2.28 GB |

  Every run replays in Lean (`composed check-dec-run`: each row a step or `DecJet.decRowI`), and
  `compd-verify` checks each proof against the statement alone and refuses it with a byte
  changed. `nockloop_soundS`: axioms `propext`, `Classical.choice`, `Quot.sound`, as
  `nockloop_sound`. Proof bytes vary slightly between runs (1.12 vs 1.13 MB at `loop_1`): `compd-prove`
  draws a fresh seed per proof for the ZK blinding (lean-ski `bench/plonky3/src/seed.rs`), and
  the serialization is likely varint-sized (zori; not measured). Each proof verifies on its own.

  The Nock claim is proved (`Nock2Ski/DecLoopSound.lean`; `propext`, `Classical.choice`,
  `Quot.sound`) for the loop's subjects `[n [0 r]]`:

      nockloop_sound : an accepted proof of nockLoopV decLoopF [n [0 r]] p →
                       NockEval [n [0 r]] decLoopF (.val p)

  The proof is specific to this loop. No replacement lemma for an arbitrary formula is
  proved. The word `W` is the autocons `S (S (K force) A0) (S (K consK) B0)`, more than 17,661
  nodes. Every glue combinator is smaller, and every glue node differs from `W` in its top
  levels. The test's code, the axes and `encNoun x` are `W`-free, so the replacement
  commutes with the compiler's shapes. The 13 occurrences are the body's call site in `L`'s
  code and the codes of the pinned literal `L`'s `Form`s. Only the top `Form`'s code runs
  (opcode 9), and with the replacement it is `Ct`.
  - Forward (`iter`, `loop_red`): by induction on `n`, with `normDec_enc` at each call, the
    replaced loop on `encNoun [n [0 r]]` reaches an encoding of `[0 [0 r]]`.
  - Converse (`check_eq`, `replaced_sound`): the replaced check is `eqn` of that run against
    `encNoun p`. By Church–Rosser it reaches `K` only if `p = [0 [0 r]]`, and `decLoop_nock`
    gives the derivation.

  Jetted, a call costs about 3,700 contractions (the normaliser and the loop's own work);
  unjetted the cost is quadratic. The transitions are the CPU's rows; a proof would add the
  DEC rows of each call.

**What remains** (lean-ski `todo/dec-norm.md`). DEC reads through thunks (an indirection
row kind on the need tree and the bit chains, three slots for the tail slot's thunk in the
`Cell` row, `compare-compd`), with `decpreExport_sound` and `decpre_complete_log` re-proved
and the released `compDAirsG` proofs re-produced: done. The Nock claim, `nockdec_sound`'s
analogue for the loop: done, `nockloop_sound` above. This closes `todo/dec-norm.md`'s
Nock-claim item for this loop (that file is lean-ski's and is not edited here). The loop's
proof itself: done, with the shared statement heap above. The other circuit-side answer is the machine doing what Avon does: reducing the
argument in place before the row reads it, which needs a machine with update in place
(lean-ski's `Ski/Graph.lean`, whose circuit is open in PLAN §1).

**Loop rows.** Proved: unjetted only (`results-unjetted.txt`, the shared base-circuit
statement, a different term from the check above): `loop_1` 76,395 contractions, 190,814
rows; `loop_3` 96,718 contractions, 242,656 rows. `loop_10` is 239,560 contractions and
`loop_20` 643,783, quadratic; their proofs would take about 0.6M and 1.6M rows, past this
machine's 4 GB budget. Jetted: the machine runs above; no proof until DEC reads through
thunks.
