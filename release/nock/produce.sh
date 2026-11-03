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
#   4. Hidden subjects (M4c, release/nock/hidden): `lake exe nockpred --log
#      R M NAME FORMULA PRODUCT K` writes the predicate statement of
#      hidden/programs.txt's program (name, subject, product, bits, log
#      CPU height, log memory height, formula): "some K literal bits are an
#      atom n with *[n f] = p", the verifier `nockPredV f K`
#      (Nock2Ski/Pred.lean), x = encNoun p, in the format of lean-ski's
#      composed predicate circuit (`ComposedText.publicTextC`); `nockpred
#      --witness` writes the K bits of the subject, which stay in a
#      temporary directory; `ski-air composed-prove PUBLIC WITNESS PROOF`
#      proves it in zero knowledge (Lean checks the statement's bytes
#      first: `lake exe composed statement -` in lean-ski) and writes
#      NAME.proof; its stdout line is hidden/results.txt's.
#
# Stages: `release/nock/produce.sh [STAGE…]` of rows, prove, hidden; all
# by default.  One job at a time.
set -euo pipefail
cd "$(dirname "$0")/../.."
LEAN_SKI=${LEAN_SKI:-../lean-ski}
R=release/nock
STAGES=" ${*:-rows prove hidden} "
want() { case "$STAGES" in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
for st in $STAGES; do
    case " rows prove hidden " in *" $st "*) ;; *) echo "no stage $st" >&2; exit 2 ;; esac
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
echo "--- Lean + ski-air: Nock programs over a hidden atom (the composed predicate circuit)"
lake build nockpred > /dev/null
: > "$R/hidden/results.txt"
while IFS=$'\t' read -r name subject product bits logr logm formula; do
    [ -n "$name" ] || continue
    D=$R/hidden/$name
    mkdir -p "$D"
    lake exe nockpred --log "$logr" "$logm" "$name" "$formula" "$product" "$bits" > "$D/public.txt"
    # the witness: the prover's secret, never written under release/
    lake exe nockpred --witness "$name" "$subject" "$bits" > "$tmp/$name.witness"
    "$A" composed-prove "$D/public.txt" "$tmp/$name.witness" "$D/$name.proof" | tee -a "$R/hidden/results.txt"
done < "$R/hidden/programs.txt"
fi
