"""skinock command line.

    python -m skinock run FORMULA SUBJECT [--avon] [--copy] [--discover] [--interp]
    python -m skinock compile FORMULA [SUBJECT] [--out FILE] [--dag|--text|--source]
    python -m skinock nock FORMULA SUBJECT          # the Python reference evaluator
    python -m skinock check                         # urbit/benchmark norm/tests.json
    python -m skinock bench [NAME…]                 # Hoon-compiled benchmarks, scaled

FORMULA and SUBJECT are nouns in `[a b c]` notation (digits may carry dots).
"""
from __future__ import annotations
import argparse, sys
from . import nock as N


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="skinock", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run", help="compile to SKI, run, and print the product")
    r.add_argument("formula"); r.add_argument("subject")
    r.add_argument("--avon", action="store_true", help="run on Avon (share mode) instead of aviary")
    r.add_argument("--copy", action="store_true", help="Avon copy mode (aviary's counts)")
    r.add_argument("--discover", action="store_true", help="Avon's generic constructor and data jets")
    r.add_argument("--interp", action="store_true", help="encode literals without code: formulas run through nockI")
    r.add_argument("--max-steps", type=int, default=50_000_000)
    c = sub.add_parser("compile", help="emit the compiled program")
    c.add_argument("formula"); c.add_argument("subject", nargs="?")
    c.add_argument("--out"); c.add_argument("--dag", action="store_true", help="Avon's dag form (default)")
    c.add_argument("--text", action="store_true", help="printed form (unfolds sharing)")
    c.add_argument("--source", action="store_true", help="the SKIjack source")
    n = sub.add_parser("nock", help="the Python reference evaluator")
    n.add_argument("formula"); n.add_argument("subject")
    sub.add_parser("check", help="urbit/benchmark reference tests")
    b = sub.add_parser("bench", help="Hoon-compiled benchmarks at scaled subjects")
    b.add_argument("names", nargs="*")
    a = ap.parse_args(argv)

    if a.cmd == "nock":
        try:
            ev = N.Evaluator()
            print(N.show(ev.nock(N.parse(a.subject), N.parse(a.formula))), f"({ev.steps} steps)")
        except N.Crash as e:
            print(f"crash: {e}")
        return 0
    if a.cmd == "check":
        from .check import check_norm
        return 0 if check_norm() else 1
    if a.cmd == "bench":
        from .bench import main as bench_main, SCALED
        bench_main(a.names or list(SCALED))
        return 0
    f, s = N.parse(a.formula), N.parse(a.subject) if a.subject else None
    if a.cmd == "compile":
        from .compile import program
        if a.source:
            out = program(f, s)
        else:
            from .run import Program
            from .avon import dag_text, term_text
            if s is None:
                ap.error("compile --dag/--text needs a subject (the program is `run subj`)")
            p = Program(f, s)
            out = term_text(p.main) if a.text else dag_text(p.main)
        (open(a.out, "w") if a.out else sys.stdout).write(out + "\n")
        return 0
    from .run import Program, SkiFuel
    p = Program(f, s, code=not a.interp)
    if a.avon or a.copy or a.discover:
        from .avon import run_avon
        v, count, status = run_avon(p.main, strategy="copy" if a.copy else "share",
                                    fuel=a.max_steps, discover=a.discover)
        print(N.show(v) if v is not None else "crash", f"({status}, Avon)")
        return 0
    try:
        res = p.run(max_steps=a.max_steps)
    except SkiFuel:
        print(f"out of fuel after {a.max_steps} contractions"); return 1
    print(N.show(res.value) if res.value is not None else "crash", f"({res.steps} contractions)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
