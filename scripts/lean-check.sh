#!/usr/bin/env bash
# Build skinock and print the axiom footprint of its theorems.
#     ./scripts/lean-check.sh
# Expected: `m0_join` uses no axioms; the M1 specs use at most `propext`,
# `Classical.choice` and `Quot.sound` (from `simp`/`omega`); the pins
# (`decide +kernel`) use none.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
lake build
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
#print axioms Nock2Ski.app_form
#print axioms Nock2Ski.app_noun
-- M1: tagged axis pulls
#print axioms Nock2Ski.pull_tagged
LEAN
lake env lean "$tmp/Axioms.lean"
