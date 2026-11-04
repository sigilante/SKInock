#!/usr/bin/env bash
# The layout evidence: exhaustive searches (search.c) and the delivery term
# (deliver.py).  Prints layout.txt's lines.  Usage: run.sh [OUTDIR for the binary]
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
bin="${1:-$(mktemp -d)}/search"
cc -O2 -o "$bin" "$here/search.c"
echo "control: J constant receives K P from [P, k]"
"$bin" 3 0 6 | tail -1
echo "hand P back bare to k below it ([P, k]):"
"$bin" 1 0 10 | tail -1
echo "hand a fresh wrapper K P bare to a continuation k ([k, P] and [P, k]):"
"$bin" 2 1 10 | tail -1
"$bin" 2 0 10 | tail -1
echo "lay out a two-field cell, both fields input-dependent, for constant J ([P, k] and [k, P]):"
"$bin" 4 0 9 | tail -1
"$bin" 4 1 9 | tail -1
echo "hand K P to k folded as the thunk K (K P) w ([k, P]):"
"$bin" 5 1 10 | tail -1
python3 -I "$here/deliver.py"
