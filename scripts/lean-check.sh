#!/usr/bin/env bash
# Build skinock, run the normalized reference tests through the Lean
# compiler and through the interpreter fallback (M2's and M3's executable
# gates), and print the axiom footprint of its theorems.
#     ./scripts/lean-check.sh
# Expected: `m0_join` uses no axioms; the specs and the simulation use at
# most `propext`, `Classical.choice` and `Quot.sound` (from `simp`/`omega`);
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
# M4a gate: nockstatement's head contraction count is ski-air's (lean-ski's
# release row sumto_us: 10297), and the release's rows recompute from their
# formulas (release/nock/verify.sh runs ski-air too; this is its Lean half)
lake build nockstatement
n=$(lake exe nockstatement --count-term ../lean-ski/release/sumto/sumto_us.term)
[ "$n" = 10297 ] && echo "nockstatement: sumto_us counts $n, as lean-ski's row" || { echo "nockstatement: sumto_us counts $n, not 10297"; exit 1; }
while IFS=$'\t' read -r name subject product budget formula; do
    case "$budget" in base) f=release/nock/corpus.txt ;; *) f=release/nock/over.txt ;; esac
    lake exe nockstatement --check "$name" "$formula" "$subject" < "$f" 2> /dev/null
done < release/nock/programs.txt
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
LEAN
lake env lean "$tmp/Axioms.lean"
