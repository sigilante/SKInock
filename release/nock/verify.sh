#!/usr/bin/env bash
# Verify release/nock: the verifier's side of produce.sh.  Run from anywhere,
# from a clean checkout of skinock with lean-ski beside it (LEAN_SKI,
# default ../lean-ski) and lean-nock at ../../lean-nock.
#
#   1. Lean recomputes every row from its formula and subject
#      (programs.txt) and compares it with corpus.txt and over.txt:
#      `lake exe nockstatement --check NAME FORMULA SUBJECT < corpus.txt`,
#      count and term; the term is never trusted from the file.  The
#      files hold those rows and no others.
#   2. ski-air re-proves and verifies every row of corpus.txt with the
#      base circuit.  The base path has no verify-only entry point: the
#      proof is made and checked in one process and never written, so the
#      verifier's run is prove-and-verify, and its stdout must match
#      results.txt row for row in contractions, rows, budget and memory
#      (the times vary).
#   3. Lean accepts each witness table ski-air wrote (`lake exe aircheck`).
#   4. With OVER=1: ski-air on over.txt, each row refused for its heights
#      (about 5.4 GB peak); off by default.
#
# Exits nonzero on any failure.  With VERIFY_ALL=1 every check runs and the
# exit comes at the end.
set -euo pipefail
cd "$(dirname "$0")/../.."
LEAN_SKI=${LEAN_SKI:-../lean-ski}
R=release/nock
tmp=$(mktemp -d)
trap '/bin/rm -rf "$tmp"' EXIT
failed=0
ok() { printf 'ok   %s\n' "$*"; }
no() { printf 'FAIL %s\n' "$*"; failed=1; [ -n "${VERIFY_ALL:-}" ] || exit 1; }

echo "--- building the Lean checker and the verifier (first run: minutes)"
lake build nockstatement > /dev/null
A=$LEAN_SKI/bench/plonky3/target/release/ski-air
[ -x "$A" ] || (cd "$LEAN_SKI/bench/plonky3" && cargo build --release --locked --quiet)
(cd "$LEAN_SKI" && lake build aircheck circuit > /dev/null)

echo "--- 1. every row recomputed by Lean from its formula"
nbase=0; nover=0
while IFS=$'\t' read -r name subject product budget formula; do
    [ -n "$name" ] || continue
    case "$budget" in base) f=$R/corpus.txt; nbase=$((nbase+1)) ;; over) f=$R/over.txt; nover=$((nover+1)) ;; *) no "$name: budget is base or over"; continue ;; esac
    if lake exe nockstatement --check "$name" "$formula" "$subject" < "$f" > "$tmp/check.log" 2> "$tmp/check.err"; then
        ok "$(cat "$tmp/check.log") [$f, product $product]"
    else
        no "$name: $(tail -n 1 "$tmp/check.err")"
    fi
done < "$R/programs.txt"
[ "$(grep -c . "$R/corpus.txt")" = "$nbase" ] && ok "corpus.txt holds the $nbase base row(s) and no other" || no "corpus.txt has rows programs.txt does not name"
[ "$(grep -c . "$R/over.txt")" = "$nover" ] && ok "over.txt holds the $nover over-budget row(s) and no other" || no "over.txt has rows programs.txt does not name"

echo "--- 2. ski-air proves and verifies every row of corpus.txt (prove-and-verify; the base path writes no proof)"
if "$A" "$R/corpus.txt" "$tmp/out" > "$tmp/results.txt"; then
    ok "ski-air: every row verified, every tampered table rejected"
else
    no "ski-air: $(grep -E 'FAIL|REJECT|contractions, reference' "$tmp/results.txt" | head -n 3 | tr '\n' ';')"
fi
# The run is the recorded one: the same rows, contractions, rows, budget and memory.
cols() { awk '$NF == "verified" {print $1, $2, $3, $4, $5}' "$1"; }
if cmp -s <(cols "$tmp/results.txt") <(cols "$R/results.txt"); then
    ok "the rows, contractions, machine rows, budget and memory are results.txt's"
else
    no "the run differs from results.txt: $(diff <(cols "$tmp/results.txt") <(cols "$R/results.txt") | head -n 4 | tr '\n' ';')"
fi
for row in $(awk '{print $1}' "$R/corpus.txt"); do
    grep -q "^$row .* verified\$" "$tmp/results.txt" && ok "$row verified" || no "$row not verified"
done

echo "--- 3. Lean accepts each witness table (aircheck: Air.Accepts)"
for row in $(awk '{print $1}' "$R/corpus.txt"); do
    if (cd "$LEAN_SKI" && lake exe aircheck "$tmp/out/$row.txt") | grep -q '^ACCEPT'; then
        ok "aircheck accepts $row's table"
    else
        no "aircheck rejects $row's table"
    fi
    head -n 1 "$tmp/out/$row.txt" | cmp -s - <(awk -v r="$row" '$1 == r {print $3}' "$R/corpus.txt") \
        && ok "$row's table names the corpus row's term" || no "$row's table names another term"
done

if [ -n "${OVER:-}" ]; then
echo "--- 4. the rows over the budget: each refused for its heights (about 5.4 GB)"
"$A" "$R/over.txt" "$tmp/out-over" > "$tmp/over.txt" || true
for row in $(awk '{print $1}' "$R/over.txt"); do
    why=$(grep -E -m 1 "^$row: FAILED an honest table: heights \[[0-9, ]*\] out of bounds\$" "$tmp/over.txt" || true)
    [ -n "$why" ] && ok "$why" || no "$row: not refused for its heights ($(grep -m 1 "^$row" "$tmp/over.txt" || echo no line))"
done
fi

[ "$failed" = 0 ] || { echo "NOT VERIFIED: release/nock"; exit 1; }
echo "VERIFIED: release/nock"
