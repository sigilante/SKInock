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
# kernel-heavy modules one at a time; each stays within about 4 GB.  The
# whole package is one Lean environment since lean-nock's `namespace Nock`
# (its branch `namespace-nock`): Nock2Ski.Circuit composes lean-ski's circuit
# theorems with the simulation, Nock2Ski.PredNock the released statements
# with lean-nock's runs, Nock2Ski.HoonDec Hoon's own `++dec` as a proved jet
# (lean-nock's branch `hoon-dec-general`, battery- and clue-generic `++dec`),
# Nock2Ski.HoonDecFree the same jet on real cores (any encoding; any terms at
# axes 2 and 7) and the fire check Avon implements.
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
# M4f gate: the probe step.  Each released probe table (release/nock/probe,
# Avon's `witness --plan` for Lean's plan of the product) is accepted by
# lean-ski's Air.checkPA for the plan Lean recomputes from the product
# (`probe_check`, then `probe_decodes_nock`: `probe_table_nock` in
# Nock2Ski.Circuit), and the plan file is that plan, the tree file the tree
# words ski-air's probe commands take (M4g)
lake build nockprobe
tmp="$(mktemp -d)"; trap 'command rm -rf "$tmp"' EXIT
while IFS=$'\t' read -r name subject product form formula; do
    [ "$product" != crash ] || continue
    lake exe nockprobe plan "$product" 2> /dev/null | cmp - "release/nock/probe/$name.plan"
    lake exe nockprobe tree "$product" 2> /dev/null | cmp - "release/nock/probe/$name.tree"
    gunzip -c "release/nock/probe/$name.probe.table.gz" > "$tmp/$name.probe.table"
    lake exe nockprobe check release/nock/corpus.txt "$name" "$tmp/$name.probe.table" "$product" | sed "s|$tmp/||"
done < release/nock/programs.txt
# M5 gate: jet transport.  Each row's jet file (release/nock/jets, lean-ski's licensed template roots
# in the Nock term) recomputes from the corpus term, and lean-ski's
# Air.checkJA accepts the released jetted witness table bound to its row
# (`nockprobe check-jets`: `Air.checkJA_sound`, `Air.air_sound_jet`, then
# `embed_outcome`)
while IFS=$'\t' read -r name subject product form formula; do
    lake exe nockprobe term release/nock/corpus.txt "$name" > "$tmp/$name.term"
    lake exe nockprobe jets "$tmp/$name.term" 2> /dev/null | cmp - "release/nock/jets/$name.jets"
    gunzip -c "release/nock/jets/$name.jetted.table.gz" > "$tmp/$name.jetted.table"
    lake exe nockprobe check-jets release/nock/corpus.txt "$name" "$tmp/$name.jetted.table" | sed "s|$tmp/||"
done < release/nock/programs.txt
# The dec jet on lean-ski's circuit (release/nock/decloop): each released
# decterm statement recomputes from N (`nockdec check`: the verifier
# `verT (checkJ decF s p)`, lean-ski's parser reading it back), and each
# unjetted corpus row from N or the Λ loop's formula
lake build nockdec
while IFS=$'\t' read -r name n; do
    lake exe nockdec check "$name" "$n" "release/nock/decloop/$name.public.txt"
done < release/nock/decloop/jetted.txt
F=$(lake exe nockdec loop-formula)
while IFS=$'\t' read -r name kind n; do
    case "$kind" in
        dec) lake exe nockdec check-corpus "$name" "$n" < release/nock/decloop/corpus.txt ;;
        loop) lake exe nockstatement --check "$name" "$F" "[$n [0 0]]" < release/nock/decloop/corpus.txt 2> /dev/null ;;
    esac
done < release/nock/decloop/unjetted.txt
# Route (B): the loop with the normalised jet on the heap machine, the
# jet's row lean-ski's DecJet.decRowI (release/nock/decloop/results-norm.txt)
lake build nocknorm
.lake/build/bin/nocknorm run 1 3 10 20 | cmp - release/nock/decloop/results-norm.txt && echo "nocknorm: results-norm.txt recomputed"
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
-- M4f: the product as a public value, the Nock side of the join
#print axioms Nock2Ski.encS_of_enc
#print axioms Nock2Ski.nock_of_valueIs
#print axioms Nock2Ski.probe_decodes_nock
#print axioms Nock2Ski.probe_decodes_nock_shared
#print axioms Nock2Ski.probe_complete_nock
#print axioms Nock2Ski.probe_complete_nock_shared
-- M5: jet transport, the lean-ski side of the join (Ski.DataJet beside Nock.Eval)
#print axioms Nock2Ski.toCell_enc
#print axioms Nock2Ski.toCell_err
#print axioms Nock2Ski.encNoun_inj
#print axioms Nock2Ski.jet_transport
#print axioms Nock2Ski.nounContract_respects
#print axioms Nock2Ski.jet_close
#print axioms Nock2Ski.jet_real
#print axioms Nock2Ski.dec_transport
#print axioms Nock2Ski.add_transport
#print axioms Nock2Ski.decContract_respects
#print axioms Nock2Ski.addContract_respects
#print axioms Nock2Ski.jet_transport_dom
#print axioms Nock2Ski.formContract_respects
-- M5: the lean-nock side, composed in (JetWord)
#print axioms Nock2Ski.leaf_word
#print axioms Nock2Ski.decF_eq
#print axioms Nock2Ski.decC_eq
#print axioms Nock2Ski.leaf_dec
#print axioms Nock2Ski.leaf_add
#print axioms Nock2Ski.leaf_total
#print axioms Nock2Ski.dec_three_valued
#print axioms Nock2Ski.add_three_valued
-- M4f: lean-ski's side (ProbeTree)
#print axioms Nock2Ski.decV_encNoun
#print axioms Nock2Ski.probe_complete
#print axioms Nock2Ski.encS_unique
#print axioms Nock2Ski.err_unique
#print axioms Nock2Ski.probe_value
#print axioms Nock2Ski.probe_sound
#print axioms Nock2Ski.probe_check
-- The joins composed (Circuit): accepted proofs and tables as Nock claims
#print axioms Nock2Ski.boolsT_eq
#print axioms Nock2Ski.probe_proof_nock
#print axioms Nock2Ski.probe_proof_nock_shared
#print axioms Nock2Ski.probe_table_nock
#print axioms Nock2Ski.probe_table_nock_shared
#print axioms Nock2Ski.pred_proof_nock
#print axioms Nock2Ski.predS_proof_nock
#print axioms Nock2Ski.pred2_proof_nock
-- The released programs from lean-nock's runs (PredNock)
#print axioms Nock2Ski.countUpF_eq
#print axioms Nock2Ski.countUp_7
#print axioms Nock2Ski.countup_hidden_7_complete
#print axioms Nock2Ski.countup_dec_7_probe
#print axioms Nock2Ski.hoonDecBat_parts
#print axioms Nock2Ski.hoonDecBat_leaf
#print axioms Nock2Ski.hoonDecHidden_gen
#print axioms Nock2Ski.hoonDecF_call
#print axioms Nock2Ski.hoonDecF_val
#print axioms Nock2Ski.hoonDecHidden_eval
#print axioms Nock2Ski.hoon_dec_hidden_12_complete
#print axioms Nock2Ski.hoonDec12_eval
#print axioms Nock2Ski.hoonDec0_crash
#print axioms Nock2Ski.hoon_dec_12_probe
#print axioms Nock2Ski.hoon_dec_0_crash
#print axioms Nock2Ski.hoonAdd_3_4
#print axioms Nock2Ski.hoonAdd_6_57
#print axioms Nock2Ski.hoon_add_hidden_3_4_complete
#print axioms Nock2Ski.hoon_add_hidden_6_57_complete
-- M5: Hoon's own `++dec` as a proved jet (HoonDec): the arm under the hint
#print axioms Nock2Ski.jet_transport_on
#print axioms Nock2Ski.onContract_respects
#print axioms Nock2Ski.hoonDecBodyF_eq
#print axioms Nock2Ski.hoon_dec_leaf
#print axioms Nock2Ski.hoon_dec_off_domain
#print axioms Nock2Ski.hoon_dec_off_domain_term
#print axioms Nock2Ski.hoon_dec_transport
#print axioms Nock2Ski.hoonDecContract_respects
#print axioms Nock2Ski.hoon_dec_hinted_leaf
#print axioms Nock2Ski.hoonDecBenchF_parts
#print axioms Nock2Ski.hoon_dec_bench_call
#print axioms Nock2Ski.hoon_dec_bench
#print axioms Nock2Ski.hoon_dec_bench_zero
-- M5: the `++dec` jet on real cores (HoonDecFree): any encoding, any battery and context
#print axioms Nock2Ski.jet_step_enc
#print axioms Nock2Ski.hoon_dec_enc
#print axioms Nock2Ski.hoonDecBodyF_split
#print axioms Nock2Ski.hoonDecLoopF_split
#print axioms Nock2Ski.dec_pull
#print axioms Nock2Ski.dec_editT
#print axioms Nock2Ski.dec_edit
#print axioms Nock2Ski.dec_loop
#print axioms Nock2Ski.dec_guard
#print axioms Nock2Ski.hoon_dec_free
#print axioms Nock2Ski.hoon_dec_free_zero
#print axioms Nock2Ski.hoon_dec_free_noSample
#print axioms Nock2Ski.CellLike.hd
#print axioms Nock2Ski.CellLike.tl
#print axioms Nock2Ski.CellLike.force
#print axioms Nock2Ski.hd_atomT
#print axioms Nock2Ski.tl_atomT
#print axioms Nock2Ski.dec_body_err
#print axioms Nock2Ski.hoon_dec_body_cl
#print axioms Nock2Ski.hoon_dec_body_cl_zero
#print axioms Nock2Ski.hoon_dec_free_cl
#print axioms Nock2Ski.hoon_dec_free_cl_zero
#print axioms Nock2Ski.hoon_dec_free_form
#print axioms Nock2Ski.hoon_dec_err_atom
#print axioms Nock2Ski.hoon_dec_err_noSample
#print axioms Nock2Ski.cellParts?_sound
#print axioms Nock2Ski.hoonDecSample?_cl
#print axioms Nock2Ski.hoon_dec_err_fires
#print axioms Nock2Ski.hoon_dec_fire_sound
#print axioms Nock2Ski.hoonDecSample?_sound
#print axioms Nock2Ski.hoonDecSample?_cellT
#print axioms Nock2Ski.hoon_dec_fires_sound
#print axioms Nock2Ski.hoon_dec_fires
#print axioms Nock2Ski.hoonDecFires_pins
-- the bare arm, as a compiled program carries it (no toCell), and the check after reducing the argument
#print axioms Nock2Ski.hoon_dec_bare_enc
#print axioms Nock2Ski.hoon_dec_bare_cl
#print axioms Nock2Ski.hoon_dec_bare_cl_zero
#print axioms Nock2Ski.hoon_dec_bare_err_atom
#print axioms Nock2Ski.hoon_dec_bare_err_noSample
#print axioms Nock2Ski.hoon_dec_bare_fires_sound
#print axioms Nock2Ski.hoon_dec_bare_err_fires
#print axioms Nock2Ski.hoon_dec_bare_fire_sound
#print axioms Nock2Ski.hoon_dec_bare_fire_sound_red
#print axioms Nock2Ski.hoon_dec_fire_sound_red
-- the dec data jet on lean-ski's circuit (DecBridge, DecLoop, DecTermNock)
#print axioms Nock2Ski.bits_eq_bitsN
#print axioms Nock2Ski.encNn_eq
#print axioms Nock2Ski.encO_eq
#print axioms Nock2Ski.dec_impl_lean
#print axioms Nock2Ski.decC_toNoun
#print axioms Nock2Ski.decpre_proof_nock
#print axioms Nock2Ski.decF_bare
#print axioms Nock2Ski.dec_impl_bare
#print axioms Nock2Ski.decLoop_ceval
#print axioms Nock2Ski.decLoop_nock
#print axioms Nock2Ski.decLoop_ski
#print axioms Nock2Ski.abstJ_close
#print axioms Nock2Ski.abstJ_occ
#print axioms Nock2Ski.nockDecV_vsOK
#print axioms Nock2Ski.nockdec_sound
-- the continuation-passing normaliser (DecNorm)
#print axioms Nock2Ski.DecNorm.fix_red
#print axioms Nock2Ski.DecNorm.normBits_bl
#print axioms Nock2Ski.DecNorm.norm_enc
#print axioms Nock2Ski.DecNorm.normJ_impl
#print axioms Nock2Ski.DecNorm.normDec_enc
-- the normalised loop as a decterm statement (DecLoopNorm)
#print axioms Nock2Ski.closeX
#print axioms Nock2Ski.checkN_close
#print axioms Nock2Ski.nockLoopV_vsOK
#print axioms Nock2Ski.nockloop_close
#print axioms Nock2Ski.nockloop_closeS
-- the normalised loop's statement read as a Nock claim (DecLoopSound)
#print axioms Nock2Ski.DecLoopSound.W_shape
#print axioms Nock2Ski.DecLoopSound.tsize_W
#print axioms Nock2Ski.DecLoopSound.free_test
#print axioms Nock2Ski.DecLoopSound.free_encNoun
#print axioms Nock2Ski.DecLoopSound.C_eq
#print axioms Nock2Ski.DecLoopSound.iter
#print axioms Nock2Ski.DecLoopSound.loop_red
#print axioms Nock2Ski.DecLoopSound.check_eq
#print axioms Nock2Ski.DecLoopSound.replaced_sound
#print axioms Nock2Ski.nockloop_sound
#print axioms Nock2Ski.nockloop_soundS
LEAN
lake env lean "$tmp/Axioms.lean"
