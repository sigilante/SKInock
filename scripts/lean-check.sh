#!/usr/bin/env bash
# Build skinock and print the axiom footprint of its theorems.
#     ./scripts/lean-check.sh
# Expected footprint of `Nock2Ski.m0_join`: no axioms at all.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
lake build
tmp="$(mktemp -d)"; trap 'command rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import Nock2Ski
#print axioms Nock2Ski.m0_join
LEAN
lake env lean "$tmp/Axioms.lean"
