#!/usr/bin/env bash
# Build skinock, run the normalized reference tests through the Lean
# compiler and through the interpreter fallback (M2's and M3's executable
# gates), and print the axiom footprint of its theorems.
#     ./scripts/lean-check.sh
# Expected: `m0_join` uses no axioms; the specs and the simulation use at
# most `propext`, `Classical.choice` and `Quot.sound` (from `simp`/`omega`;
# M4e's converse is classical by contraposition, `Classical.choice` proper);
# the pins (`decide +kernel`) use `propext`, through `parse_pin`'s derived
# `DecidableEq` of the parsed declarations.  The build runs the
# kernel-heavy modules one at a time; each stays within about 4 GB.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
lake build
# M2 gate: every urbit/benchmark norm test (63) and the M2 programs agree;
# M3 gate: the 63 tests again with the formula as code-free data, interpreted
lake build normcheck
lake exe normcheck | grep -E "^(norm|programs|interp):"
# M4a/M4b gate: nockstatement's head contraction count is ski-air's
# (lean-ski's release row sumto_us: 10297), and the release's rows recompute
# from their formulas, `share (compiled f s)` for the rows of form `shared`
# and `compiled f s` for `plain` (release/nock/verify.sh runs ski-air too;
# this is its Lean half)
lake build nockstatement
n=$(lake exe nockstatement --count-term ../lean-ski/release/sumto/sumto_us.term)
[ "$n" = 10297 ] && echo "nockstatement: sumto_us counts $n, as lean-ski's row" || { echo "nockstatement: sumto_us counts $n, not 10297"; exit 1; }
while IFS=$'\t' read -r name subject product form formula; do
    case "$form" in shared) flag=() ;; plain) flag=(--unshared) ;; *) echo "$name: form is plain or shared"; exit 1 ;; esac
    lake exe nockstatement --check "${flag[@]}" "$name" "$formula" "$subject" < release/nock/corpus.txt 2> /dev/null
done < release/nock/programs.txt
# M4c/M4d gate: each hidden-subject statement (release/nock/hidden)
# recomputes from its formula, product and public skeleton (`nockpred
# --check`: the verifier is `nockPredS f SKEL`, `nockPredV f K` for the
# one-atom skeleton `K`, x is `encNoun p`), and the verifier accepts the
# subject's bits in the clear (`nockpred --run`, lean-ski's runF reaching K:
# `nock_pred_complete` and `nock_pred2_complete` at the released programs)
lake build nockpred
while IFS=$'\t' read -r name subject product skel logr logm formula; do
    lake exe nockpred --check "$name" "$formula" "$product" "$skel" < "release/nock/hidden/$name/public.txt" 2> /dev/null
    lake exe nockpred --run "$name" "$formula" "$product" "$subject" "$skel" 2> /dev/null
done < release/nock/hidden/programs.txt
tmp="$(mktemp -d)"; trap 'command rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import Nock2Ski
#print axioms Nock2Ski.m0_join
-- M1: the compiler's terms, read by the front end
#print axioms Nock2Ski.compileFile_refuses
#print axioms Nock2Ski.hd_pin
#print axioms Nock2Ski.inc_pin
#print axioms Nock2Ski.eq_pin
#print axioms Nock2Ski.ifn_pin
#print axioms Nock2Ski.app_pin
-- M1: the encoding's eliminators
#print axioms Nock2Ski.encNoun_atom_elim
#print axioms Nock2Ski.encNoun_cell_elim
-- M1: the specs
#print axioms Nock2Ski.hd_spec
#print axioms Nock2Ski.tl_spec
#print axioms Nock2Ski.cel_spec
#print axioms Nock2Ski.force_spec
#print axioms Nock2Ski.inc_spec
#print axioms Nock2Ski.inc_cell
#print axioms Nock2Ski.eq_spec
#print axioms Nock2Ski.eq_tisN
#print axioms Nock2Ski.ifn_zero
#print axioms Nock2Ski.ifn_one
#print axioms Nock2Ski.ifn_big
#print axioms Nock2Ski.ifn_cell
-- M3: the interpreter fallback, pinned and specified
#print axioms Nock2Ski.parse_pin
#print axioms Nock2Ski.nockI_pin
#print axioms Nock2Ski.nockO_pin
#print axioms Nock2Ski.app_pin
#print axioms Nock2Ski.nockI_eq
#print axioms Nock2Ski.app_cell
#print axioms Nock2Ski.app_form
#print axioms Nock2Ski.decop_spec
#print axioms Nock2Ski.path_spec
#print axioms Nock2Ski.descend_spec
#print axioms Nock2Ski.slotB_enc
#print axioms Nock2Ski.editB_enc
-- M1: tagged axis pulls
#print axioms Nock2Ski.pull_tagged
-- M2: the compiler
#print axioms Nock2Ski.malformed_eq
#print axioms Nock2Ski.axisPath_eq_axisSteps
#print axioms Nock2Ski.nockToSki_malformed
-- M2: the encoding relation and the primitives over it
#print axioms Nock2Ski.enc_encLit
#print axioms Nock2Ski.eq_enc
#print axioms Nock2Ski.fasO_axisPath
#print axioms Nock2Ski.haxO_axisPath
#print axioms Nock2Ski.pick_enc
-- M2, M3: the simulation
#print axioms Nock2Ski.editT_enc
#print axioms Nock2Ski.embed_both
#print axioms Nock2Ski.embed_crash
#print axioms Nock2Ski.embed_value
#print axioms Nock2Ski.nockI_crash
#print axioms Nock2Ski.nockI_value
#print axioms Nock2Ski.compiled_crash
#print axioms Nock2Ski.compiled_value
#print axioms Nock2Ski.interpreted_value
-- M4b: sharing in the term, and the join to the circuit's statement
#print axioms Nock2Ski.chain_red
#print axioms Nock2Ski.share_red
#print axioms Nock2Ski.shared_value
#print axioms Nock2Ski.shared_crash
#print axioms Nock2Ski.enc_whnf
#print axioms Nock2Ski.eval_enc
#print axioms Nock2Ski.shared_value_eval
#print axioms Nock2Ski.shared_crash_eval
#print axioms Nock2Ski.compiled_value_eval
#print axioms Nock2Ski.compiled_crash_eval
-- M4c: the predicate statement over a hidden atom
#print axioms Nock2Ski.trim_bitsK
#print axioms Nock2Ski.consTrimT_red
#print axioms Nock2Ski.toBitsT_red
#print axioms Nock2Ski.nockPredV_beta
#print axioms Nock2Ski.nock_pred_complete
#print axioms Nock2Ski.eqn_err
#print axioms Nock2Ski.nock_pred_sound_val
#print axioms Nock2Ski.nock_pred_sound_crash
#print axioms Nock2Ski.nock_pred_sound
-- M4d: a cell-shaped hidden subject, the public skeleton
#print axioms Nock2Ski.dropT_red
#print axioms Nock2Ski.takeT_red
#print axioms Nock2Ski.sliceT_red
#print axioms Nock2Ski.skel_red
#print axioms Nock2Ski.nockPredS_beta
#print axioms Nock2Ski.nockPredS_hole
#print axioms Nock2Ski.nock_predS_complete
#print axioms Nock2Ski.nock_pred2_complete
#print axioms Nock2Ski.nock_predS_sound
#print axioms Nock2Ski.nock_pred2_sound
-- M4e: the converse simulation, the hidden-subject statements as Nock claims
#print axioms Nock2Ski.hred_stepsN
#print axioms Nock2Ski.pendCheck_sound
#print axioms Nock2Ski.contCheck_sound
#print axioms Nock2Ski.hlen_force_pend
#print axioms Nock2Ski.hlen_force_enc
#print axioms Nock2Ski.hlen_eqn_pend
#print axioms Nock2Ski.pending_of_noOut
#print axioms Nock2Ski.pending_both
#print axioms Nock2Ski.embed_terminates
#print axioms Nock2Ski.nockI_terminates
#print axioms Nock2Ski.embed_outcome
#print axioms Nock2Ski.embed_complete
#print axioms Nock2Ski.embed_diverges
#print axioms Nock2Ski.compiled_terminates
#print axioms Nock2Ski.shared_terminates
#print axioms Nock2Ski.nock_of_eqn_K
#print axioms Nock2Ski.nock_pred_sound_nock
#print axioms Nock2Ski.nock_predS_sound_nock
#print axioms Nock2Ski.nock_pred2_sound_nock
LEAN
lake env lean "$tmp/Axioms.lean"
