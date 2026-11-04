#!/usr/bin/env bash
# Verify release/nock/decloop: the verifier's side of produce.sh.  Run from a
# clean checkout of skinock with lean-ski beside it (LEAN_SKI, default
# ../lean-ski) on its `dec-loop` branch, and lean-nock at ../../lean-nock.
#
#   1. The jetted statements: for each row of jetted.txt, Lean recomputes
#      the `decterm` statement of *[[N 0] phi(dec)] = [N-1 0] at the heights
#      the text names and compares it byte for byte, and lean-ski's parser
#      reads it back as exactly that verifier (`lake exe nockdec check NAME
#      N PUBLIC`); it refuses the text as N + 1's.  `ski-air compd-verify`
#      checks NAME.proof against the statement alone (Lean's `composed
#      statement-dec -`, then the AIRs from the text: `compDAirsG`, whose
#      soundness `Circuit.dectermExport_sound` is; `nockdec_sound`, with
#      `dec_impl_bare` closing the jet to the word, concludes *[s f] = p),
#      and refuses it with one byte changed.  lean-ski's `composed
#      check-dec-run` replays the released run.
#   2. The unjetted rows: Lean recomputes every row of corpus.txt from N
#      (`nockdec check-corpus`, `nockstatement --check` for the loop) and
#      the file holds those rows and no others; ski-air re-proves and
#      verifies every row with the base circuit (the base path has no
#      verify-only entry point), its stdout matching results-unjetted.txt
#      row for row in contractions, rows, budget and memory; lean-ski's
#      aircheck accepts each table.  `VERIFY_UNJETTED=0` skips the
#      re-proof (dec_100_unjetted peaks at 3.3 GB).
#   3. probe.txt is recomputed (`nockdec probe 3`).
#   4. layout.txt is recomputed (layout/run.sh: the searches and the
#      delivery term), and lean-ski's Ski/NoLayout.lean builds.
#   5. results-norm.txt is recomputed (`nocknorm run 1 3 10 20`: the loop
#      with the normalised jet on the heap machine, lean-ski's
#      DecJet.decRowI firing at every call), and lean-ski's Ski/DecInd.lean
#      and Nock2Ski/DecNorm.lean build.
set -euo pipefail
cd "$(dirname "$0")/../../.."
LEAN_SKI=${LEAN_SKI:-../lean-ski}
D=release/nock/decloop
tmp=$(mktemp -d)
trap '/bin/rm -rf "$tmp"' EXIT
A=$LEAN_SKI/bench/plonky3/target/release/ski-air
(cd "$LEAN_SKI/bench/plonky3" && cargo build --release --locked --quiet)
(cd "$LEAN_SKI" && lake build composed circuit aircheck > /dev/null)
lake build nockdec nockstatement nocknorm > /dev/null
N=.lake/build/bin/nockdec
fail() { echo "FAIL: $*" >&2; exit 1; }

echo "--- 1. the jetted statements"
while IFS=$'\t' read -r name n; do
    [ -n "$name" ] || continue
    "$N" check "$name" "$n" "$D/$name.public.txt"
    if "$N" check "$name" "$((n + 1))" "$D/$name.public.txt" > /dev/null 2>&1; then fail "$name: accepted as N + 1's"; fi
    "$A" compd-verify "$D/$name.public.txt" "$D/$name.proof" | sed "s/^decterm [0-9]*:/$name:/"
    command cp -f "$D/$name.proof" "$tmp/bad.proof"
    printf '\x01' | dd of="$tmp/bad.proof" bs=1 seek=200 conv=notrunc 2> /dev/null
    if "$A" compd-verify "$D/$name.public.txt" "$tmp/bad.proof" > /dev/null 2>&1; then fail "$name: a changed proof verified"; fi
    echo "$name: the proof with byte 200 changed is refused"
    (cd "$LEAN_SKI" && lake exe composed check-dec-run "$OLDPWD/$D/$name.public.txt" "$OLDPWD/$D/$name.run.txt") \
        | grep -E '^(OK|REJECT|NOT|MALFORMED)' | sed "s/^/$name: /"
done < "$D/jetted.txt"

echo "--- 2. the unjetted rows"
F=$("$N" loop-formula)
names=""
while IFS=$'\t' read -r name kind n; do
    [ -n "$name" ] || continue
    names="$names $name"
    case "$kind" in
        dec) "$N" check-corpus "$name" "$n" < "$D/corpus.txt" ;;
        loop) lake exe nockstatement --check "$name" "$F" "[$n [0 0]]" < "$D/corpus.txt" 2> /dev/null ;;
    esac
done < "$D/unjetted.txt"
[ "$(awk '{print $1}' "$D/corpus.txt" | tr '\n' ' ')" = "${names# } " ] || fail "corpus.txt holds other rows"
if [ "${VERIFY_UNJETTED:-1}" != 0 ]; then
    "$A" "$D/corpus.txt" "$tmp/out" > "$tmp/results.txt"
    for row in $(awk '{print $1}' "$D/corpus.txt"); do
        a=$(awk -v r="$row" '$1 == r {print $2, $3, $4, $5, $8}' "$D/results-unjetted.txt")
        b=$(awk -v r="$row" '$1 == r {print $2, $3, $4, $5, $8}' "$tmp/results.txt")
        [ "$a" = "$b" ] || fail "$row: re-proved as '$b', released '$a'"
        echo "$row: re-proved and verified, $b"
        (cd "$LEAN_SKI" && lake exe aircheck "$tmp/out/$row.txt" | grep -E '^(ACCEPT|REJECT)')
    done
fi

echo "--- 3. the probe"
"$N" probe 3 > "$tmp/probe.txt"
cmp "$tmp/probe.txt" "$D/probe.txt" && echo "probe.txt: recomputed"
echo "--- 4. the layout evidence"
"$D/layout/run.sh" "$tmp" > "$tmp/layout.txt"
cmp "$tmp/layout.txt" "$D/layout.txt" && echo "layout.txt: recomputed"
(cd "$LEAN_SKI" && lake build Ski.NoLayout > /dev/null) && echo "lean-ski Ski/NoLayout.lean: built"
echo "--- 5. the loop with the normalised jet"
.lake/build/bin/nocknorm run 1 3 10 20 > "$tmp/results-norm.txt"
cmp "$tmp/results-norm.txt" "$D/results-norm.txt" && echo "results-norm.txt: recomputed"
(cd "$LEAN_SKI" && lake build Ski.DecInd > /dev/null) && echo "lean-ski Ski/DecInd.lean: built"
lake build Nock2Ski.DecNorm > /dev/null && echo "Nock2Ski/DecNorm.lean: built"
echo "ALL CHECKS PASSED"
