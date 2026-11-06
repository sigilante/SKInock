#!/usr/bin/env bash
# Produce release/nock/decloop: lean-ski's `dec` data jet on a Nock claim,
# rows jetted against unjetted.  The producer's side; verify.sh is the
# verifier's.  Run from a clean checkout of skinock with lean-ski beside it
# (LEAN_SKI, default ../lean-ski) on master (b9275ad or later) (the `decterm`
# statement, Ski/DecTermText.lean and Ski/DecTerm.lean, and ski-air's
# `decterm J` header), and lean-nock at ../../lean-nock.
#
#   jetted    For each row of jetted.txt (name, N): `lake exe nockdec emit`
#             writes the `decterm` statement of *[[N 0] phi(dec)] = [N-1 0]
#             (Nock2Ski/DecTermNock.lean: one verifier `λ β w. checkJ`, the
#             check `eqn (nockToSki decF ⬝ encNoun s) (encNoun p)` with
#             every occurrence of the compiled word `dec` the jet's atom),
#             first at the least heights, then at the heights `ski-air
#             compd-measure` reports the run needs (each log at least 9);
#             `ski-air compd-prove` proves it (Lean checks the bytes first,
#             `lake exe composed statement-dec -`) and writes NAME.proof and
#             the run (NAME.run.txt); lean-ski's `composed check-dec-run`
#             replays the run (every row a step or DecJet.decRowI).  Stdout
#             lines: results.txt.
#   unjetted  The same check with the bare word in the jet's place
#             (`nockdec corpus`, rows `dec`), and the Λ loop `while (top ≠
#             0) dec` on [N [0 0]] (Nock2Ski/DecLoop.lean, `nockstatement`
#             over `nockdec loop-formula`, rows `loop`, shared), as corpus
#             rows of lean-ski's base circuit: `ski-air corpus.txt out`
#             proves and verifies each in-process (results-unjetted.txt),
#             and lean-ski's `aircheck` accepts each table.  The largest
#             row, dec_100_unjetted (533,392 rows at 2^20), peaks at 3.3 GB.
#   probe     `nockdec probe 3`: the compiled loop with the word's 13
#             occurrences as the jet, in a head machine whose jet fires
#             only on a subject laid out in memory, as lean-ski's row
#             does; the run stops at the first call (probe.txt).  The
#             reader through K-thunks stops there too: results-norm.txt's
#             "bare jet" rows (stage norm).
#   layout    Why no term can lay the argument out (layout/): exhaustive
#             searches over SKI terms on a model of lean-ski's write-once
#             machine (layout/search.c), and the 12-leaf term that hands a
#             fresh wrapper to a dynamic continuation only as the thunk
#             `K (K P) w` (layout/deliver.py); lean-ski's Ski/NoLayout.lean
#             proves the invariant behind them (layout.txt).
#   norm      Route (B): `nocknorm run 1 3 10 20` (bench/NockNorm.lean)
#             runs the Nock claim *[[N [0 0]] decLoopF] = [0 [0 0]]'s check
#             on lean-ski's heap machine, unjetted, with every occurrence
#             of the compiled word the jet's atom (it stops at the first
#             call), and with every occurrence `normJ JD` (Nock2Ski/
#             DecNorm.lean's continuation-passing normaliser, then the
#             jet): lean-ski's DecJet.decRowI (Ski/DecInd.lean, the row
#             reading through K-thunks) fires at every call and the run
#             reaches K (results-norm.txt).  Machine runs; on the circuit
#             (lean-ski branch dec-thunk) the loop's statement is `nockdec
#             emit-loop` and is measured, not proved (its 2^22-row memory
#             table is past the memory budget; DECJET.md, Route B).
#   loop      Route (B) proved: for each row of loops.txt (name, N),
#             `nockdec emit-loop` writes the loop's statement with its heap
#             shared (header `dectermS`, lean-ski's `sharedL`, master
#             b9275ad: about 2,300 public cells instead of 2.33 million),
#             at the heights `ski-air compd-measure` reports; `ski-air
#             compd-prove` proves it and lean-ski's `composed check-dec-run`
#             replays the run (results-loop.txt).  Nock2Ski/DecLoopSound's
#             `nockloop_soundS` makes an accepted proof a Nock derivation
#             of *[[N [0 0]] decLoopF] = [0 [0 0]].  loop_20 peaks under
#             3 GB.
#
# Stages: `produce.sh [jetted unjetted probe layout norm loop]`, all by default.
set -euo pipefail
cd "$(dirname "$0")/../../.."
LEAN_SKI=${LEAN_SKI:-../lean-ski}
D=release/nock/decloop
STAGES=" ${*:-jetted unjetted probe layout norm loop} "
want() { case "$STAGES" in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
for st in $STAGES; do
    case " jetted unjetted probe layout norm loop " in *" $st "*) ;; *) echo "no stage $st" >&2; exit 2 ;; esac
done
tmp=$(mktemp -d)
trap '/bin/rm -rf "$tmp"' EXIT
A=$LEAN_SKI/bench/plonky3/target/release/ski-air
(cd "$LEAN_SKI/bench/plonky3" && cargo build --release --locked --quiet)
(cd "$LEAN_SKI" && lake build composed circuit aircheck > /dev/null)
lake build nockdec nockstatement nocknorm > /dev/null
N=.lake/build/bin/nockdec
lg() { awk -v x="$1" 'BEGIN { l = 9; while (2 ^ l < x) l++; print l }'; }

if want jetted; then
echo "--- the jetted check: decterm statements on lean-ski's circuit with the dec jet"
: > "$D/results.txt"
while IFS=$'\t' read -r name n; do
    [ -n "$name" ] || continue
    "$N" emit "$tmp" "$name" "$n" 9 9 9 > /dev/null
    m=$("$A" compd-measure "$tmp/$name.public.txt" "$tmp/$name.witness.txt" 2>&1 || true)
    rows=$(echo "$m" | grep -o '[0-9]* rows' | head -1 | cut -d' ' -f1)
    cells=$(echo "$m" | grep -o '[0-9]* memory cells' | cut -d' ' -f1)
    jrows=$(echo "$m" | grep -o '[0-9]* jet rows' | cut -d' ' -f1)
    "$N" emit "$D" "$name" "$n" "$(lg "$rows")" "$(lg "$cells")" "$(lg "$jrows")" > /dev/null
    /bin/mv "$D/$name.witness.txt" "$tmp/$name.witness.txt"
    "$A" compd-prove "$D/$name.public.txt" "$tmp/$name.witness.txt" "$D/$name.proof" --table="$D/$name.run.txt" \
        | sed "s/^decterm [0-9]*:/$name (N = $n):/" | tee -a "$D/results.txt"
    (cd "$LEAN_SKI" && lake exe composed check-dec-run "$OLDPWD/$D/$name.public.txt" "$OLDPWD/$D/$name.run.txt") \
        | grep -E '^(OK|REJECT|NOT|MALFORMED)' | sed "s/^/$name: /" | tee -a "$D/results.txt"
done < "$D/jetted.txt"
fi

if want unjetted; then
echo "--- the unjetted check and the Λ loop: corpus rows of lean-ski's base circuit"
F=$("$N" loop-formula)
: > "$D/corpus.txt"
while IFS=$'\t' read -r name kind n; do
    [ -n "$name" ] || continue
    case "$kind" in
        dec) "$N" corpus "$name" "$n" >> "$D/corpus.txt" ;;
        loop) lake exe nockstatement "$name" "$F" "[$n [0 0]]" 2> /dev/null >> "$D/corpus.txt" ;;
        *) echo "$name: kind is dec or loop" >&2; exit 2 ;;
    esac
done < "$D/unjetted.txt"
awk '{printf "%s %s contractions, %d bytes\n", $1, $2, length($3)}' "$D/corpus.txt"
"$A" "$D/corpus.txt" "$tmp/out" | tee "$D/results-unjetted.txt"
for row in $(awk '{print $1}' "$D/corpus.txt"); do
    (cd "$LEAN_SKI" && lake exe aircheck "$tmp/out/$row.txt" | grep -E '^(ACCEPT|REJECT)')
done
fi

if want probe; then
echo "--- the compiled loop with the word as the jet"
"$N" probe 3 | tee "$D/probe.txt"
fi

if want layout; then
echo "--- why no term lays the argument out"
"$D/layout/run.sh" "$tmp" | tee "$D/layout.txt"
(cd "$LEAN_SKI" && lake build Ski.NoLayout > /dev/null) && echo "lean-ski Ski/NoLayout.lean: built (inv_step, inv_reach, S_cont_const)"
fi

if want norm; then
echo "--- route (B): the loop with the normalised jet, on the heap machine"
.lake/build/bin/nocknorm run 1 3 10 20 | tee "$D/results-norm.txt"
(cd "$LEAN_SKI" && lake build Ski.DecInd > /dev/null) && echo "lean-ski Ski/DecInd.lean: built (decRowI_step, JStepsI.close_K)"
lake build Nock2Ski.DecNorm > /dev/null && echo "Nock2Ski/DecNorm.lean: built (norm_enc, normJ_impl, normDec_enc)"
fi

if want loop; then
echo "--- route (B) proved: the loop with the normalised jet, its statement shared"
: > "$D/results-loop.txt"
while IFS=$'\t' read -r name n; do
    [ -n "$name" ] || continue
    "$N" emit-loop "$tmp" "$name" "$n" 9 9 9 > /dev/null
    m=$("$A" compd-measure "$tmp/$name.public.txt" "$tmp/$name.witness.txt" 2>&1 || true)
    rows=$(echo "$m" | grep -o '[0-9]* rows' | head -1 | cut -d' ' -f1)
    cells=$(echo "$m" | grep -o '[0-9]* memory cells' | cut -d' ' -f1)
    jrows=$(echo "$m" | grep -o '[0-9]* jet rows' | cut -d' ' -f1)
    "$N" emit-loop "$D" "$name" "$n" "$(lg "$rows")" "$(lg "$cells")" "$(lg "$jrows")" > /dev/null
    /bin/mv "$D/$name.witness.txt" "$tmp/$name.witness.txt"
    "$A" compd-prove "$D/$name.public.txt" "$tmp/$name.witness.txt" "$D/$name.proof" --table="$D/$name.run.txt" \
        | sed "s/^dectermS [0-9]*:/$name (N = $n):/" | tee -a "$D/results-loop.txt"
    (cd "$LEAN_SKI" && lake exe composed check-dec-run "$OLDPWD/$D/$name.public.txt" "$OLDPWD/$D/$name.run.txt") \
        | grep -E '^(OK|REJECT|NOT|MALFORMED)' | sed "s/^/$name: /" | tee -a "$D/results-loop.txt"
done < "$D/loops.txt"
lake build Nock2Ski.DecLoopSound > /dev/null && echo "Nock2Ski/DecLoopSound.lean: built (nockloop_soundS)"
fi
