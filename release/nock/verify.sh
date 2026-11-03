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
#   4. The hidden-subject statements (release/nock/hidden, M4c and M4d):
#      for each program of hidden/programs.txt, Lean recomputes the
#      verifier from the public formula and the public skeleton (`8`: one
#      hidden atom of 8 bits; `[?4 ?4]`: a cell of two hidden atoms of 4
#      bits each) and compares the statement (`lake exe nockpred --check
#      NAME FORMULA PRODUCT SKEL < public.txt`: `predicate (nockPredS f
#      SKEL) (encNoun p) N` at the recorded heights, its text the composed
#      machine's), refuses it for the product + 1, and lean-ski's own check
#      accepts the bytes (`lake exe composed statement`); ski-air
#      composed-verify checks the proof against the statement, and refuses
#      it with one byte changed.  The subject in programs.txt is the
#      producer's witness, published for reproduction; the proof reveals
#      nothing of it (lean-ski's `comp_zk`).
#   5. The product as a public value (release/nock/probe, M4f): for each
#      row whose product is a noun, Lean recomputes the probe plan from the
#      product (`lake exe nockprobe plan PRODUCT`: `Air.planOf (nounV p)
#      0`, Nock2Ski/ProbeTree.lean) and the term's jet file (`nockprobe
#      jets`) and compares them with the released files; `nockprobe check`
#      accepts the released probe table for the row and the product
#      (lean-ski's `Air.checkPA`: `probe_check`, so the term's value is the
#      product, and `probe_decodes_nock`: *[s f] = p), and refuses it for
#      the product + 1 and for a cell.  The table is the prover's (Avon's
#      `witness --plan`).  Then the STARK (M4g): Lean recomputes the tree
#      words (`nockprobe tree PRODUCT`: `tree`, then `nounV p`'s nodes in
#      preorder) and compares them with NAME.tree; `ski-air probe-verify`
#      checks NAME.probe.proof against the corpus row, the jet file (Lean's
#      `jets statement-stdin`) and the tree (Lean's `jets plan`, lean-ski's
#      probe-plan-file branch, and `circuit compare-probe`, so
#      `Circuit.probeExport_sound_tree`, then `probe_value` and
#      `probe_decodes_nock`: *[s f] = p), and refuses it for the tree of
#      the product + 1, for the cell's, and with one byte changed.
#   6. The jetted rows (release/nock/jets, M5): lean-ski's `lake exe jets
#      statement` checks every jet file against its corpus term (the file
#      is exactly the term's, its roots licensed: `Air.rootsOKB`), and
#      `nockprobe jets` recomputes each; `nockprobe check-jets` accepts the
#      released jetted table for its row (lean-ski's `Air.checkJA`:
#      `Air.checkJA_sound`, `Air.air_sound_jet`, so the table ends on a
#      value the row's term evaluates to up to weak reduction and with its
#      head, `jet_run_eval`, `jet_run_shape`; then `embed_outcome`) and
#      refuses it as another row's; `ski-air jet-verify` checks each proof
#      against the corpus row and the jet file (Lean's `jets
#      statement-stdin` first; `Circuit.jetExport_sound`), and refuses it
#      as another row's and with one byte changed.
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

echo "--- 4. Nock programs over a hidden subject: the composed predicate circuit (release/nock/hidden)"
lake build nockpred > /dev/null
(cd "$LEAN_SKI" && lake build composed > /dev/null)
n=0
while IFS=$'\t' read -r name subject product skel logr logm formula; do
    [ -n "$name" ] || continue
    n=$((n+1))
    D=$R/hidden/$name
    if lake exe nockpred --check "$name" "$formula" "$product" "$skel" < "$D/public.txt" > "$tmp/pc.log" 2> /dev/null; then
        ok "$(head -c 120 "$tmp/pc.log")..."
    else
        no "$name: $(head -n 1 "$tmp/pc.log")"
    fi
    [ "$(sed -n 3p "$D/public.txt")" = "log $logr $logm" ] && ok "$name: heights 2^$logr and 2^$logm, as programs.txt records" || no "$name: the heights are not programs.txt's"
    case "$product" in
    ''|*[!0-9]*) ;;
    *)  if lake exe nockpred --check "$name" "$formula" "$((product + 1))" "$skel" < "$D/public.txt" > "$tmp/pc2.log" 2> /dev/null; then
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

echo "--- 5. The product as a public value: the probe plan, the probe table and its proof (release/nock/probe)"
lake build nockprobe > /dev/null
P=$R/probe
n=0
while IFS=$'\t' read -r name subject product form formula; do
    [ -n "$name" ] || continue
    [ "$product" != crash ] || continue
    n=$((n+1))
    if lake exe nockprobe plan "$product" 2> "$tmp/plan.err" | cmp -s - "$P/$name.plan"; then
        ok "$name: $name.plan is Lean's plan of the product $product ($(sed 's/.*: //' "$tmp/plan.err"))"
    else
        no "$name: $name.plan is not the plan of $product"
    fi
    if lake exe nockprobe tree "$product" 2> /dev/null | cmp -s - "$P/$name.tree"; then
        ok "$name: $name.tree is the tree nounV of the product $product ($(wc -w < "$P/$name.tree" | tr -d ' ') words)"
    else
        no "$name: $name.tree is not the tree of $product"
    fi
    lake exe nockprobe term "$R/corpus.txt" "$name" > "$tmp/$name.term"
    if lake exe nockprobe jets "$tmp/$name.term" 2> "$tmp/jets.err" | cmp -s - "$P/$name.jets"; then
        ok "$name: $name.jets is the term's jet file ($(sed 's/.*: //' "$tmp/jets.err"))"
    else
        no "$name: $name.jets is not the term's jet file"
    fi
    gunzip -c "$P/$name.probe.table.gz" > "$tmp/$name.probe.table"
    if lake exe nockprobe check "$R/corpus.txt" "$name" "$tmp/$name.probe.table" "$product" > "$tmp/pr.log" 2>&1; then
        ok "$(sed "s|$tmp/||" "$tmp/pr.log")"
    else
        no "$name: $(head -n 1 "$tmp/pr.log")"
    fi
    case "$product" in
    ''|*[!0-9]*) ;;
    *)  if lake exe nockprobe check "$R/corpus.txt" "$name" "$tmp/$name.probe.table" "$((product + 1))" > "$tmp/pr2.log" 2>&1; then
            no "$name: the probe table read as the product $((product + 1))"
        else
            ok "$name: the probe table is refused for the product $((product + 1))"
        fi
        if lake exe nockprobe check "$R/corpus.txt" "$name" "$tmp/$name.probe.table" "[$product 0]" > "$tmp/pr3.log" 2>&1; then
            no "$name: the probe table read as the cell [$product 0]"
        else
            ok "$name: the probe table is refused for the cell [$product 0]"
        fi ;;
    esac
    # the STARK: ski-air probe-verify against the corpus row, the jet file and the tree
    # shellcheck disable=SC2046
    if "$A" probe-verify "$R/corpus.txt" "$P" "$name" "$P/$name.probe.proof" $(cat "$P/$name.tree") > "$tmp/pv.log" 2>&1 && grep -q '^VERIFIED' "$tmp/pv.log"; then
        ok "$name: ski-air probe-verify accepts $name.probe.proof for the tree of $product $(grep -o '([0-9]* segments; [0-9.]* s)' "$tmp/pv.log")"
    else
        no "$name: probe-verify rejects the proof ($(head -c 100 "$tmp/pv.log"))"
    fi
    case "$product" in
    ''|*[!0-9]*) ;;
    *)  for claim in "$((product + 1))" "[$product 0]"; do
            # shellcheck disable=SC2046
            if "$A" probe-verify "$R/corpus.txt" "$P" "$name" "$P/$name.probe.proof" $(lake exe nockprobe tree "$claim" 2> /dev/null) > "$tmp/pv2.log" 2>&1; then
                no "$name: the probe proof verified for the tree of $claim"
            else
                ok "$name: the probe proof is refused for the tree of $claim ($(grep -o 'REJECTED: [^(]*' "$tmp/pv2.log" | head -c 60))"
            fi
        done ;;
    esac
    /bin/cp "$P/$name.probe.proof" "$tmp/pflip.proof"
    size=$(wc -c < "$tmp/pflip.proof")
    off=$((size / 2))
    byte=$(dd if="$tmp/pflip.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
    printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
        | dd of="$tmp/pflip.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
    # shellcheck disable=SC2046
    if "$A" probe-verify "$R/corpus.txt" "$P" "$name" "$tmp/pflip.proof" $(cat "$P/$name.tree") > "$tmp/pf.log" 2>&1; then
        no "$name: the probe proof with one byte changed verified"
    else
        ok "$name: the probe proof with byte $off changed is refused ($(grep -o 'REJECTED: [^(]*' "$tmp/pf.log" | head -c 60))"
    fi
done < "$R/programs.txt"
[ "$(grep -c '^ACCEPT' "$P/results.txt")" -ge "$n" ] && ok "probe/results.txt records the $n accepted table(s)" || no "probe/results.txt does not record one ACCEPT per table"
[ "$(grep -c 'probe-verify: VERIFIED' "$P/results.txt")" = "$n" ] && ok "probe/results.txt records the $n verified proof(s)" || no "probe/results.txt does not record one VERIFIED per proof"


echo "--- 6. The jetted rows: the jet files, the jetted tables and their proofs (release/nock/jets, M5)"
J=$R/jets
(cd "$LEAN_SKI" && lake build jets > /dev/null)
if (cd "$LEAN_SKI" && lake exe jets statement "$OLDPWD/$R/corpus.txt" "$OLDPWD/$J") > "$tmp/js.log" 2>&1 && ! grep -qv '^STATEMENT' "$tmp/js.log"; then
    ok "lean-ski's jets statement: each row's jet file is its term's, roots licensed ($(grep -c '^STATEMENT' "$tmp/js.log") files)"
else
    no "lean-ski's jets statement refuses a jet file: $(grep -v '^STATEMENT' "$tmp/js.log" | head -n 2 | tr '\n' ';')"
fi
n=0
while IFS=$'\t' read -r name subject product form formula; do
    [ -n "$name" ] || continue
    n=$((n+1))
    lake exe nockprobe term "$R/corpus.txt" "$name" > "$tmp/$name.term"
    if lake exe nockprobe jets "$tmp/$name.term" 2> "$tmp/jets.err" | cmp -s - "$J/$name.jets"; then
        ok "$name: $name.jets is the term's jet file ($(sed 's/.*: //' "$tmp/jets.err"))"
    else
        no "$name: $name.jets is not the term's jet file"
    fi
    other=$(awk -v r="$name" '$1 != r {print $1; exit}' "$R/corpus.txt")
    gunzip -c "$J/$name.jetted.table.gz" > "$tmp/$name.jetted.table"
    if lake exe nockprobe check-jets "$R/corpus.txt" "$name" "$tmp/$name.jetted.table" > "$tmp/cj.log" 2>&1; then
        ok "$(sed "s|$tmp/||" "$tmp/cj.log")"
    else
        no "$name: $(head -n 1 "$tmp/cj.log")"
    fi
    if lake exe nockprobe check-jets "$R/corpus.txt" "$other" "$tmp/$name.jetted.table" > "$tmp/cj2.log" 2>&1; then
        no "$name: the jetted table read as $other's"
    else
        ok "$name: the jetted table is refused as $other's"
    fi
    if "$A" jet-verify "$R/corpus.txt" "$J" "$name" "$J/$name.jetted.proof" > "$tmp/jv.log" 2>&1 && grep -q '^VERIFIED' "$tmp/jv.log"; then
        ok "$name: ski-air jet-verify accepts $name.jetted.proof $(grep -o '([0-9.]* s)' "$tmp/jv.log")"
    else
        no "$name: jet-verify rejects the proof ($(head -c 100 "$tmp/jv.log"))"
    fi
    if "$A" jet-verify "$R/corpus.txt" "$J" "$other" "$J/$name.jetted.proof" > "$tmp/jv2.log" 2>&1; then
        no "$name: the jetted proof verified as $other's"
    else
        ok "$name: the jetted proof is refused as $other's ($(grep -o 'REJECTED: [^(]*' "$tmp/jv2.log" | head -c 60))"
    fi
    /bin/cp "$J/$name.jetted.proof" "$tmp/jflip.proof"
    size=$(wc -c < "$tmp/jflip.proof")
    off=$((size / 2))
    byte=$(dd if="$tmp/jflip.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
    printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
        | dd of="$tmp/jflip.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
    if "$A" jet-verify "$R/corpus.txt" "$J" "$name" "$tmp/jflip.proof" > "$tmp/jf.log" 2>&1; then
        no "$name: the jetted proof with one byte changed verified"
    else
        ok "$name: the jetted proof with byte $off changed is refused ($(grep -o 'REJECTED: [^(]*' "$tmp/jf.log" | head -c 60))"
    fi
done < "$R/programs.txt"
[ "$(grep -c 'jet-verify: VERIFIED' "$J/results.txt")" = "$n" ] && ok "jets/results.txt records the $n verified jetted proof(s)" || no "jets/results.txt does not record one VERIFIED per row"

[ "$failed" = 0 ] || { echo "NOT VERIFIED: release/nock"; exit 1; }
echo "VERIFIED: release/nock"
