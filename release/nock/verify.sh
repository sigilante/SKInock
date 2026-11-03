#!/usr/bin/env bash
# Verify release/nock: the verifier's side of produce.sh.  Run from anywhere,
# from a clean checkout of skinock with lean-ski beside it (LEAN_SKI,
# default ../lean-ski) and lean-nock at ../../lean-nock.
#
#   1. Lean recomputes every row from its formula and subject
#      (programs.txt) and compares it with corpus.txt:
#      `lake exe nockstatement --check [--unshared] NAME FORMULA SUBJECT <
#      corpus.txt`, count and term, `--unshared` for the rows of form
#      `plain`; the term is never trusted from the file.  The file holds
#      those rows and no others.
#   2. ski-air re-proves and verifies every row of corpus.txt with the
#      base circuit.  The base path has no verify-only entry point: the
#      proof is made and checked in one process and never written, so the
#      verifier's run is prove-and-verify, and its stdout must match
#      results.txt row for row in contractions, rows, budget and memory
#      (the times vary).
#   3. Lean accepts each witness table ski-air wrote (`lake exe aircheck`).
#   4. The hidden-subject statements (release/nock/hidden, M4c): for each
#      program of hidden/programs.txt, Lean recomputes the verifier from
#      the public formula and compares the statement (`lake exe nockpred
#      --check NAME FORMULA PRODUCT K < public.txt`: `predicate (nockPredV
#      f K) (encNoun p) K` at the recorded heights, its text the composed
#      machine's), refuses it for the product + 1, and lean-ski's own check
#      accepts the bytes (`lake exe composed statement`); ski-air
#      composed-verify checks the proof against the statement, and refuses
#      it with one byte changed.  The subject in programs.txt is the
#      producer's witness, published for reproduction; the proof reveals
#      nothing of it (lean-ski's `comp_zk`).
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
n=0
while IFS=$'\t' read -r name subject product form formula; do
    [ -n "$name" ] || continue
    case "$form" in shared) flag=() ;; plain) flag=(--unshared) ;; *) no "$name: form is plain or shared"; continue ;; esac
    n=$((n+1))
    if lake exe nockstatement --check "${flag[@]}" "$name" "$formula" "$subject" < "$R/corpus.txt" > "$tmp/check.log" 2> "$tmp/check.err"; then
        ok "$(cat "$tmp/check.log") [product $product]"
    else
        no "$name: $(tail -n 1 "$tmp/check.err")"
    fi
done < "$R/programs.txt"
[ "$(grep -c . "$R/corpus.txt")" = "$n" ] && ok "corpus.txt holds the $n row(s) of programs.txt and no other" || no "corpus.txt has rows programs.txt does not name"

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

echo "--- 4. Nock programs over a hidden atom: the composed predicate circuit (release/nock/hidden)"
lake build nockpred > /dev/null
(cd "$LEAN_SKI" && lake build composed > /dev/null)
n=0
while IFS=$'\t' read -r name subject product bits logr logm formula; do
    [ -n "$name" ] || continue
    n=$((n+1))
    D=$R/hidden/$name
    if lake exe nockpred --check "$name" "$formula" "$product" "$bits" < "$D/public.txt" > "$tmp/pc.log" 2> /dev/null; then
        ok "$(head -c 120 "$tmp/pc.log")..."
    else
        no "$name: $(head -n 1 "$tmp/pc.log")"
    fi
    [ "$(sed -n 3p "$D/public.txt")" = "log $logr $logm" ] && ok "$name: heights 2^$logr and 2^$logm, as programs.txt records" || no "$name: the heights are not programs.txt's"
    case "$product" in
    ''|*[!0-9]*) ;;
    *)  if lake exe nockpred --check "$name" "$formula" "$((product + 1))" "$bits" < "$D/public.txt" > "$tmp/pc2.log" 2> /dev/null; then
            no "$name: the statement read as product $((product + 1))"
        else
            ok "$name: not the statement for product $((product + 1)) ($(head -n 1 "$tmp/pc2.log"))"
        fi ;;
    esac
    if (cd "$LEAN_SKI" && lake exe composed statement "$OLDPWD/$D/public.txt") > "$tmp/cs.log" 2> /dev/null && grep -q '^STATEMENT' "$tmp/cs.log"; then
        ok "$name: lean-ski's composed statement accepts public.txt ($(grep -o 'a region of.*' "$tmp/cs.log"))"
    else
        no "$name: lean-ski's composed statement refuses public.txt ($(head -c 80 "$tmp/cs.log"))"
    fi
    if "$A" composed-verify "$D/public.txt" "$D/$name.proof" > "$tmp/cv.log" 2>&1 && grep -q '^VERIFIED' "$tmp/cv.log"; then
        ok "$name: ski-air composed-verify accepts $name.proof $(grep -o '([0-9]* segments; [0-9.]* s)' "$tmp/cv.log")"
    else
        no "$name: composed-verify rejects the proof ($(head -c 100 "$tmp/cv.log"))"
    fi
    /bin/cp "$D/$name.proof" "$tmp/flip.proof"
    size=$(wc -c < "$tmp/flip.proof")
    off=$((size / 2))
    byte=$(dd if="$tmp/flip.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
    printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
        | dd of="$tmp/flip.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
    if "$A" composed-verify "$D/public.txt" "$tmp/flip.proof" > "$tmp/cf.log" 2>&1; then
        no "$name: the proof with one byte changed verified"
    else
        ok "$name: the proof with byte $off changed is refused ($(grep -o 'REJECTED: [^(]*' "$tmp/cf.log" | head -c 60))"
    fi
done < "$R/hidden/programs.txt"
[ "$(grep -c '^proved' "$R/hidden/results.txt")" = "$n" ] && ok "hidden/results.txt records the $n proof(s) of hidden/programs.txt" || no "hidden/results.txt does not record one line per program"

[ "$failed" = 0 ] || { echo "NOT VERIFIED: release/nock"; exit 1; }
echo "VERIFIED: release/nock"
