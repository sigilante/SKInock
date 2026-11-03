"""Check the compiler against urbit/benchmark's normalized tests and the
Python evaluator: `python -m skinock.check [--norm PATH] [--bench DIR]`."""
from __future__ import annotations
import argparse, json, os, sys, time
from . import nock as N
from .run import run, SkiFuel

NORM = os.path.expanduser("~/Code/urbit/benchmark/norm/tests.json")


def expected(entry):
    return None if entry["result"] is None else N.parse(entry["result"])


def check_norm(path=NORM, verbose=False):
    tests = json.load(open(path))
    bad = 0
    for i, e in enumerate(tests):
        s, f = N.parse(e["subject"]), N.parse(e["formula"])
        want = expected(e)
        # the Python evaluator first
        try:
            got_py = N.nock(s, f, fuel=10_000)
        except N.Crash:
            got_py = None
        # then the compiled SKI
        try:
            r = run(f, s)
            got = r.value
            note = f"{r.steps} contractions, {r.atoms} atoms"
        except SkiFuel:
            got, note = "FUEL", ""
        ok = got == want and got_py == want
        bad += not ok
        if verbose or not ok:
            print(f"{'ok  ' if ok else 'FAIL'} #{i} op {e['opcode']}: *[{e['subject']} {e['formula']}] = "
                  f"{e['result']}; py {N.show(got_py) if got_py is not None else None}; "
                  f"ski {N.show(got) if isinstance(got, (int, tuple)) else got}  ({note})")
    print(f"norm: {len(tests) - bad}/{len(tests)} agree")
    return bad == 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--norm", default=NORM)
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    sys.exit(0 if check_norm(a.norm, a.v) else 1)
