#!/usr/bin/env bash
# Produce release/nock: Nock programs proved on lean-ski's base circuit with
# no Nock circuit (PLAN.md §4, M4a and M4b).  The producer's side; verify.sh
# is the verifier's.  Run from anywhere, from a clean checkout of skinock
# with lean-ski beside it (LEAN_SKI, default ../lean-ski) and lean-nock at
# ../../lean-nock on its lean-4.31 branch, as lakefile.toml requires.
#
#   1. Lean: `lake exe nockstatement [--unshared] NAME FORMULA SUBJECT`
#      writes the corpus row of each program in programs.txt (name,
#      subject, product, form, formula; tab-separated): the term in prefix
#      form and its head contraction count, the count ski-air's machine
#      checks before it proves a row.  The form is `shared`, the term
#      `share (compiled f s)` (Nock2Ski/Share.lean: every repeated subterm
#      of 1024 cells or more bound once, so the prefix tree is the DAG's
#      size; the βs add to the count), or `plain`, the term `compiled f s =
#      nockToSki f ⬝ encLit s` itself.  `lake exe nockstatement --cells
#      FORMULA SUBJECT` prints the cell counts first: the circuit's memory
#      and program tables hold 2^21 cells (MAX_LOG_HEIGHT in lean-ski's
#      bench/plonky3/src/main.rs), and ski-air loads a term cell by cell.
#   2. ski-air: `ski-air corpus.txt out` proves every row with the base
#      circuit and verifies each in-process (the verifier recomputes the
#      circuit from the public term, and `lake exe circuit compare` in
#      lean-ski checks it against `Circuit.baseAirs`, the hypothesis of
#      `Circuit.export_sound`).  The proof is never written: ski-air's base
#      path writes only out/NAME.txt, the witness table in Lean's format.
#      Its stdout, the table of rows, budget, memory and times, is
#      results.txt; RESULTS.md quotes it.
#   3. Lean: `lake exe aircheck out/NAME.txt` in lean-ski accepts each
#      table (Air.checkA, so Air.Accepts: the table is an evaluation of
#      the term it names).
#
#   4. Hidden subjects (M4c, M4d, release/nock/hidden): `lake exe nockpred
#      --log R M NAME FORMULA PRODUCT SKEL` writes the predicate statement
#      of hidden/programs.txt's program (name, subject, product, skeleton,
#      log CPU height, log memory height, formula): "some N literal bits
#      are the atoms of a subject s of shape SKEL with *[s f] = p", the
#      verifier `nockPredS f SKEL` (Nock2Ski/PredSkel.lean), x = encNoun p,
#      in the format of lean-ski's composed predicate circuit
#      (`ComposedText.publicTextC`).  The skeleton is public: `8` is one
#      hidden atom of 8 bits (M4c, `nockPredV f 8`), `[?4 ?4]` a cell of
#      two hidden atoms of 4 bits each (M4d, `nockPred2V f 4`), N the
#      widths summed.  `nockpred --witness` writes the subject's bits, hole
#      by hole, which stay in a temporary directory; `ski-air
#      composed-prove PUBLIC WITNESS PROOF` proves it in zero knowledge
#      (Lean checks the statement's bytes first: `lake exe composed
#      statement -` in lean-ski) and writes NAME.proof; its stdout line is
#      hidden/results.txt's.  The two `add` rows take 14 s and 23 s and
#      peak at 1.9 GB and 3.4 GB.
#
#   5. The product as a public value (M4f, release/nock/probe): for each
#      row whose product is a noun, `lake exe nockprobe plan PRODUCT`
#      writes the probe plan of `nounV p` (Nock2Ski/ProbeTree.lean:
#      `Air.planOf`, the segments that read the term constructor by
#      constructor), `nockprobe jets` the term's jet file (lean-ski's
#      `JetTable.jetTable`: the template roots the run may instantiate),
#      and Avon (AVON, default ~/avon/build/avon) runs the segments
#      (`avon witness --plan`) and writes the table with probe segments,
#      kept gzipped; `nockprobe check` accepts it (Air.checkPA, so
#      `probe_check`: the term's value is the product, and
#      `probe_decodes_nock`: *[s f] = p).  Without Avon the committed table
#      is checked.  Then the STARK (M4g): `nockprobe tree PRODUCT` writes
#      the tree `nounV p` as outcome words (`NAME.tree`: `tree`, then the
#      nodes in preorder), which ski-air's probe commands pass to `lake exe
#      jets plan` (lean-ski's probe-plan-file branch, Ski/ProbeText.lean);
#      `ski-air probe-prove-table` proves the released table for that plan
#      (`NAME.probe.proof`) and `probe-verify` checks the proof against the
#      corpus row, the jet file and the tree, Lean comparing the AIRs
#      (`circuit compare-probe`): `Circuit.probeExport_sound_tree`, then
#      `probe_value` and `probe_decodes_nock`.
#
#   6. The jetted rows (M5, release/nock/jets): each row proved with
#      lean-ski's EXISTING supercombinator-jet machinery, no new jet built.
#      `lake exe nockprobe jets` writes the row's jet file (as in 5:
#      lean-ski's `JetTable.jetTable` over `allTemplates`, the SKIlark
#      template roots it licenses inside the Nock term); `ski-air
#      jets-measure TERM JETS TABLE` runs the term with those roots
#      instantiated and writes the jetted witness table (Avon's `witness
#      --jet-table` writes the same bytes; compared when Avon is present),
#      printing the plain and jetted row counts; `nockprobe check-jets`
#      accepts it bound to the row (lean-ski's `Air.checkJA`, so
#      `Air.checkJA_sound`, `Air.air_sound_jet`); `ski-air jet-prove`
#      proves it (`NAME.jetted.proof`) and `jet-verify` checks the proof
#      against the corpus row and the jet file, Lean checking the jet file
#      first (`lake exe jets statement-stdin`): `Circuit.jetExport_sound`,
#      then `jet_run_shape` and `embed_outcome` (README, "Jet transport").
#      The transported `dec` DATA jet of Nock2Ski/JetTransport.lean has no
#      circuit here (held); these are code jets of generic subterms.
#
# Stages: `release/nock/produce.sh [STAGE…]` of rows, prove, hidden, probe,
# jets; all by default.  One job at a time.
set -euo pipefail
cd "$(dirname "$0")/../.."
LEAN_SKI=${LEAN_SKI:-../lean-ski}
R=release/nock
STAGES=" ${*:-rows prove hidden probe jets} "
want() { case "$STAGES" in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
for st in $STAGES; do
    case " rows prove hidden probe jets " in *" $st "*) ;; *) echo "no stage $st" >&2; exit 2 ;; esac
done
tmp=$(mktemp -d)
trap '/bin/rm -rf "$tmp"' EXIT
A=$LEAN_SKI/bench/plonky3/target/release/ski-air
[ -x "$A" ] || (cd "$LEAN_SKI/bench/plonky3" && cargo build --release --locked --quiet)

if want rows; then
echo "--- Lean: the corpus rows (nockstatement)"
lake build nockstatement > /dev/null
: > "$R/corpus.txt"
while IFS=$'\t' read -r name subject product form formula; do
    [ -n "$name" ] || continue
    case "$form" in shared) flag=() ;; plain) flag=(--unshared) ;; *) echo "$name: form is plain or shared" >&2; exit 2 ;; esac
    lake exe nockstatement "${flag[@]}" "$name" "$formula" "$subject" >> "$R/corpus.txt"
done < "$R/programs.txt"
awk '{printf "%s %s contractions, %d bytes\n", $1, $2, length($3)}' "$R/corpus.txt"
fi

if want prove; then
echo "--- ski-air: every row of corpus.txt proved and verified (the base circuit)"
/bin/rm -rf "$R/out"
"$A" "$R/corpus.txt" "$R/out" | tee "$R/results.txt"
echo "--- Lean: each witness table accepted (aircheck)"
(cd "$LEAN_SKI" && lake build aircheck > /dev/null)
for row in $(awk '{print $1}' "$R/corpus.txt"); do
    (cd "$LEAN_SKI" && lake exe aircheck "$OLDPWD/$R/out/$row.txt")
done
fi

if want hidden; then
echo "--- Lean + ski-air: Nock programs over a hidden subject (the composed predicate circuit)"
lake build nockpred > /dev/null
: > "$R/hidden/results.txt"
while IFS=$'\t' read -r name subject product skel logr logm formula; do
    [ -n "$name" ] || continue
    D=$R/hidden/$name
    mkdir -p "$D"
    lake exe nockpred --log "$logr" "$logm" "$name" "$formula" "$product" "$skel" > "$D/public.txt"
    # the witness: the prover's secret, never written under release/
    lake exe nockpred --witness "$name" "$subject" "$skel" > "$tmp/$name.witness"
    "$A" composed-prove "$D/public.txt" "$tmp/$name.witness" "$D/$name.proof" | tee -a "$R/hidden/results.txt"
done < "$R/hidden/programs.txt"
fi

if want probe; then
echo "--- Lean + Avon + ski-air: the public product as a probe plan, the probe table checked and proved (M4f, M4g)"
lake build nockprobe > /dev/null
AVON=${AVON:-$HOME/avon/build/avon}
P=$R/probe
mkdir -p "$P/out"
: > "$P/results.txt"
while IFS=$'\t' read -r name subject product form formula; do
    [ -n "$name" ] || continue
    [ "$product" != crash ] || continue
    lake exe nockprobe plan "$product" > "$P/$name.plan" 2> "$tmp/plan.err"
    lake exe nockprobe tree "$product" > "$P/$name.tree" 2> /dev/null
    lake exe nockprobe term "$R/corpus.txt" "$name" > "$tmp/$name.term"
    lake exe nockprobe jets "$tmp/$name.term" > "$P/$name.jets" 2> "$tmp/jets.err"
    echo "$name: product $product: $(sed 's/^[^:]*: //' "$tmp/plan.err"); jet file: $(sed 's/.*: //' "$tmp/jets.err")" | tee -a "$P/results.txt"
    if [ -x "$AVON" ]; then
        # the plain run: the released table
        "$AVON" witness --plan="$P/$name.plan" "$tmp/$name.term" > "$P/out/$name.probe.table" 2> "$tmp/avon.err"
        echo "$name: avon witness --plan: $(tail -n 1 "$tmp/avon.err")" | tee -a "$P/results.txt"
        gzip -9 -c "$P/out/$name.probe.table" > "$P/$name.probe.table.gz"
        # the same with lean-ski's licensed template jets instantiated: a measurement
        "$AVON" witness --jet-table="$P/$name.jets" --plan="$P/$name.plan" "$tmp/$name.term" > "$P/out/$name.probe.jetted.table" 2> "$tmp/avonj.err"
        echo "$name: avon witness --jet-table --plan: $(tail -n 1 "$tmp/avonj.err")" | tee -a "$P/results.txt"
        lake exe nockprobe check "$R/corpus.txt" "$name" "$P/out/$name.probe.jetted.table" "$product" | tee -a "$P/results.txt"
    else
        echo "$name: no Avon at $AVON (set AVON); the released table is checked" | tee -a "$P/results.txt"
        gunzip -c "$P/$name.probe.table.gz" > "$P/out/$name.probe.table"
    fi
    lake exe nockprobe check "$R/corpus.txt" "$name" "$P/out/$name.probe.table" "$product" | tee -a "$P/results.txt"
    # the STARK of the released table, for the plan of the tree (`lake exe
    # jets plan tree …`), verified against the corpus row, the jet file and
    # the tree; the proof is kept
    # shellcheck disable=SC2046
    "$A" probe-prove-table "$tmp/$name.term" "$P/$name.jets" "$P/out/$name.probe.table" "$P/$name.probe.proof" $(cat "$P/$name.tree") \
        | sed "s/^/$name: probe-prove-table: /" | tee -a "$P/results.txt"
    # shellcheck disable=SC2046
    "$A" probe-verify "$R/corpus.txt" "$P" "$name" "$P/$name.probe.proof" $(cat "$P/$name.tree") \
        | sed "s/^/$name: probe-verify: /; s/ decodes to tree [0-9 ]*(/ decodes to the tree of $product (/" | tee -a "$P/results.txt"
done < "$R/programs.txt"
fi

if want jets; then
echo "--- Lean + ski-air: the rows jetted with lean-ski's licensed template roots (M5)"
lake build nockprobe > /dev/null
AVON=${AVON:-$HOME/avon/build/avon}
J=$R/jets
mkdir -p "$J"
: > "$J/results.txt"
while IFS=$'\t' read -r name subject product form formula; do
    [ -n "$name" ] || continue
    lake exe nockprobe term "$R/corpus.txt" "$name" > "$tmp/$name.term"
    lake exe nockprobe jets "$tmp/$name.term" > "$J/$name.jets" 2> "$tmp/jets.err"
    echo "$name: jet file: $(sed 's/.*: //' "$tmp/jets.err")" | tee -a "$J/results.txt"
    # the jetted witness: ski-air's own run with the licensed roots instantiated;
    # it proves and verifies it in-process too, and prints the plain run beside it
    "$A" jets-measure "$tmp/$name.term" "$J/$name.jets" "$tmp/$name.jetted.table" \
        | sed "s/^/$name: jets-measure: /" | tee -a "$J/results.txt"
    gzip -9 -c "$tmp/$name.jetted.table" > "$J/$name.jetted.table.gz"
    if [ -x "$AVON" ]; then
        "$AVON" witness --jet-table="$J/$name.jets" "$tmp/$name.term" > "$tmp/$name.avon.table" 2> "$tmp/avon.err"
        if cmp -s "$tmp/$name.avon.table" "$tmp/$name.jetted.table"; then
            echo "$name: avon witness --jet-table writes the same table ($(tail -n 1 "$tmp/avon.err"))" | tee -a "$J/results.txt"
        else
            echo "$name: avon witness --jet-table differs from ski-air's table" | tee -a "$J/results.txt"; exit 1
        fi
    fi
    lake exe nockprobe check-jets "$R/corpus.txt" "$name" "$tmp/$name.jetted.table" | sed "s|$tmp/||" | tee -a "$J/results.txt"
    "$A" jet-prove "$tmp/$name.term" "$J/$name.jets" "$tmp/$name.jetted.table" "$J/$name.jetted.proof" \
        | sed "s/^/$name: jet-prove: /" | tee -a "$J/results.txt"
    "$A" jet-verify "$R/corpus.txt" "$J" "$name" "$J/$name.jetted.proof" \
        | sed "s/^/$name: jet-verify: /" | tee -a "$J/results.txt"
done < "$R/programs.txt"
fi
