#!/bin/sh
# The whole skinock artifact, end to end, from a clean checkout with lean-ski
# beside it (../lean-ski) and lean-nock at ../../lean-nock on its lean-4.31
# branch; Python 3.10+ with skijack and aviary-kernel; elan and cargo.
#
#   scripts/artifact.sh            # everything below
#   scripts/artifact.sh quick      # skip the circuit proofs (prove+verify)
#
# 1. the Python compiler and its tests (139), including urbit/benchmark's 63
#    reference tests, compiled and as data;
# 2. the reference tests through the Python oracle and the compiled SKI,
#    and the Hoon-compiled benchmarks at scaled subjects;
# 3. the Lean development: build, the three normcheck gates (63/63 compiled,
#    6/6 programs, 63/63 interpreted), the statement checks, and the axioms
#    of every theorem (no sorry, no native_decide);
# 4. the circuit proofs: every program of release/nock proved on lean-ski's
#    circuits and verified from the Nock formula (release/nock/produce.sh
#    regenerates them; verify.sh re-checks statements and proofs), and
#    release/nock/decloop's: the dec jet on lean-ski's circuit, jetted
#    against unjetted (needs lean-ski's dec-loop branch).
set -eu
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
step() { printf '\n== %s\n' "$*"; }

step "1. Python: install and test"
pip install -q -e python
python3 -m pytest -q tests

step "2. urbit/benchmark: reference tests and Hoon-compiled programs"
python3 -m skinock check
python3 -m skinock bench dec add ackermann

step "3. Lean: build, normcheck gates, statement checks, axioms"
./scripts/lean-check.sh

if [ "${1:-}" != quick ]; then
  step "4. Circuit proofs: produce and verify release/nock"
  release/nock/produce.sh
  VERIFY_ALL=1 release/nock/verify.sh
  release/nock/decloop/produce.sh
  release/nock/decloop/verify.sh
fi

step "ARTIFACT OK"
