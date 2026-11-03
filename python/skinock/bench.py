"""urbit/benchmark's Hoon-compiled programs through the compiler, at
scaled-down subjects: `python -m skinock.bench [NAME…]`.

Each `.nock` file is `[subject formula]`; the subject is replaced by a small
value so the SKI run fits Python's reducer.  The Python evaluator is the
oracle and also counts Nock steps, so the table reports contractions per
Nock step for Hoon-shaped code.
"""
from __future__ import annotations
import os, sys, time
from . import nock as N
from .run import Program, SkiFuel

BAR = os.path.expanduser("~/Code/urbit/benchmark/desk/bar")

# scaled subjects: (name, [subjects…])
SCALED = {
    "dec":       [5, 20, 100],
    "add":       [(3, 4), (20, 30)],
    "factorial": [3, 5],
    "fibonacci": [5, 8],
    "ackermann": [(1, 2), (2, 2)],
    "bigslot":   [0],
}


def load(name):
    cell = N.parse(open(os.path.join(BAR, name + ".nock")).read())
    return cell[0], cell[1]


def main(names, max_steps=20_000_000):
    rows = []
    for name in names:
        subj0, f = load(name)
        for s in SCALED.get(name, [subj0]):
            ev = N.Evaluator(fuel=5_000_000)
            try:
                want = ev.nock(s, f)
            except N.Crash:
                want = None
            except N.Fuel:
                print(f"{name} {N.show(s)}: Python oracle out of fuel"); continue
            t0 = time.time()
            try:
                p = Program(f, s)
                r = p.run(max_steps=max_steps)
                got, steps = r.value, r.steps
            except SkiFuel:
                got, steps = "FUEL", max_steps
            dt = time.time() - t0
            ok = got == want
            per = steps / ev.steps if ev.steps else float("nan")
            rows.append((name, N.show(s), N.show(want) if want is not None else "crash",
                         "ok" if ok else f"MISMATCH {got}", ev.steps, steps, per, p.atoms, dt))
            print(f"{name:10} subject {N.show(s):10} -> {rows[-1][2]:>8} {rows[-1][3]:8} "
                  f"nock steps {ev.steps:7,} ski contractions {steps:11,} ({per:7.1f}/step) "
                  f"main {p.atoms:,} atoms  [{dt:.1f}s]", flush=True)
    return rows


if __name__ == "__main__":
    names = sys.argv[1:] or list(SCALED)
    main(names)
