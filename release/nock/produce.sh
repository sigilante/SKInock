#!/usr/bin/env bash
# Produce release/nock: Nock programs proved on lean-ski's base circuit with
# no Nock circuit (PLAN.md §4, M4a).  The producer's side; verify.sh is the
# verifier's.  Run from anywhere, from a clean checkout of skinock with
# lean-ski beside it (LEAN_SKI, default ../lean-ski) and lean-nock at
# ../../lean-nock on its lean-4.31 branch, as lakefile.toml requires.
#
#   1. Lean: `lake exe nockstatement NAME FORMULA SUBJECT` writes the corpus
#      row of each program in programs.txt (name, subject, product, budget,
#      formula; tab-separated): the term `compiled f s = nockToSki f ⬝
#      encLit s` in prefix form and its head contraction count, the count
#      ski-air's machine checks before it proves a row.  Rows marked `base`
#      go to corpus.txt, rows marked `over` to over.txt: their term alone,
#      loaded cell by cell with no sharing, exceeds the 2^21 cells of the
#      circuit's memory and program tables (MAX_LOG_HEIGHT in lean-ski's
#      bench/plonky3/src/main.rs), and the verifier refuses the heights.
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
#   4. Stage `over` (not run by default: the prover builds the 2^22-row
#      tables, about 5.4 GB peak, and the proof is refused): ski-air on
#      over.txt; its stdout is over-results.txt.  Each row must be refused
#      for its heights and no other reason.
#
# Stages: `release/nock/produce.sh [STAGE…]` of rows, prove, over; rows and
# prove by default.  One job at a time.
set -euo pipefail
cd "$(dirname "$0")/../.."
LEAN_SKI=${LEAN_SKI:-../lean-ski}
R=release/nock
STAGES=" ${*:-rows prove} "
want() { case "$STAGES" in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
for st in $STAGES; do
    case " rows prove over " in *" $st "*) ;; *) echo "no stage $st" >&2; exit 2 ;; esac
done
A=$LEAN_SKI/bench/plonky3/target/release/ski-air
[ -x "$A" ] || (cd "$LEAN_SKI/bench/plonky3" && cargo build --release --locked --quiet)

if want rows; then
echo "--- Lean: the corpus rows (nockstatement)"
lake build nockstatement > /dev/null
: > "$R/corpus.txt"; : > "$R/over.txt"
while IFS=$'\t' read -r name subject product budget formula; do
    [ -n "$name" ] || continue
    case "$budget" in base) f=$R/corpus.txt ;; over) f=$R/over.txt ;; *) echo "$name: budget is base or over" >&2; exit 2 ;; esac
    lake exe nockstatement "$name" "$formula" "$subject" >> "$f"
done < "$R/programs.txt"
awk '{printf "%s %s contractions, %d bytes\n", $1, $2, length($3)}' "$R/corpus.txt" "$R/over.txt"
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

if want over; then
echo "--- ski-air: the rows over the budget (each refused for its heights; about 5.4 GB)"
/bin/rm -rf "$R/out-over"
set +e
"$A" "$R/over.txt" "$R/out-over" | tee "$R/over-results.txt"
set -e
for row in $(awk '{print $1}' "$R/over.txt"); do
    grep -q "^$row: FAILED an honest table: heights \[[0-9, ]*\] out of bounds\$" "$R/over-results.txt" \
        || { echo "$row: not refused for its heights" >&2; exit 1; }
done
fi
