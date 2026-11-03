"""Nock formulas to SKIjack source, and on to closed SKI terms.

The compiled formula is an expression over a subject variable.  Strictness
follows Nock: both halves of an autocons, both operands of opcodes 2, 5 and
10, the pushed value of 8, the subject of 7 and 9 and the hint of a dynamic
11 are forced (one case, propagating Err) before use, in Vere's order; the
branches of 6 are left unevaluated until chosen.  A literal cell that
parses as a formula is emitted as `Form h t code` with its compiled code,
so a battery pushed by `[1 …]` carries live arms and opcode 9 applies them.
"""
from __future__ import annotations
import os
from . import nock as N

LIB = open(os.path.join(os.path.dirname(__file__), "nock.ski")).read()


def bits(n: int) -> str:
    """An atom's bits as a Scott list, least significant first, no leading zeros."""
    s = "Nil"
    for ch in bin(n)[2:]:            # most significant first, so the last wraps innermost
        s = f"(Cons {'T' if ch == '1' else 'F'} {s})"
    return s if n else "Nil"


class Compiler:
    def __init__(self):
        self.k = 0

    def fresh(self, base="s"):
        self.k += 1
        return f"{base}{self.k}"

    # ---- literals
    def lit(self, n: N.Noun) -> str:
        if isinstance(n, int):
            return f"(Atom {bits(n)})"
        h, t = self.lit(n[0]), self.lit(n[1])
        if N.is_formula(n):
            s = self.fresh()
            return f"(Form {h} {t} (\\{s}. {self.formula(n, s)}))"
        return f"(Cell {h} {t})"

    # ---- projections of a static axis, lazily (consumers force)
    def axis(self, axis: int, s: str) -> str:
        if axis == 0:
            return "Err"
        e = s
        for b in bin(axis)[3:]:
            e = f"({'hd' if b == '0' else 'tl'} {e})"
        return e

    # ---- edit at a static axis: rebuild the path with forced projections
    def edit(self, axis: int, v: str, t: str) -> str:
        if axis == 0:
            return "Err"
        if axis == 1:
            return v
        path = bin(axis)[3:]

        def go(i: int, cur: str) -> str:
            if i == len(path):
                return v
            h, tl_ = self.fresh("h"), self.fresh("t")
            if path[i] == "0":
                inner = go(i + 1, h)
                return (f"(force (hd {cur}) (\\{h}. (force (tl {cur}) (\\{tl_}. "
                        f"(Cell {inner} {tl_})))))")
            inner = go(i + 1, tl_)
            return (f"(force (hd {cur}) (\\{h}. (force (tl {cur}) (\\{tl_}. "
                    f"(Cell {h} {inner})))))")
        return go(0, t)

    # ---- formulas
    def formula(self, f: N.Noun, s: str) -> str:
        if not N.is_cell(f):
            return "Err"
        op, rest = f
        if N.is_cell(op):
            x, y = self.fresh("x"), self.fresh("y")
            return (f"(force {self.formula(op, s)} (\\{x}. (force {self.formula(rest, s)} "
                    f"(\\{y}. (Cell {x} {y})))))")
        if op == 0:
            return self.axis(rest, s) if isinstance(rest, int) else "Err"
        if op == 1:
            return self.lit(rest)
        if op == 2:
            x, g = self.fresh("x"), self.fresh("f")
            return (f"(force {self.formula(rest[0], s)} (\\{x}. (force {self.formula(rest[1], s)} "
                    f"(\\{g}. (app {g} {x})))))")
        if op == 3:
            return f"(cel {self.formula(rest, s)})"
        if op == 4:
            return f"(inc {self.formula(rest, s)})"
        if op == 5:
            x, y = self.fresh("x"), self.fresh("y")
            return (f"(force {self.formula(rest[0], s)} (\\{x}. (force {self.formula(rest[1], s)} "
                    f"(\\{y}. (eq {x} {y})))))")
        if op == 6:
            c, (y, n) = rest
            return f"(ifn {self.formula(c, s)} {self.formula(y, s)} {self.formula(n, s)})"
        if op == 7:
            x = self.fresh()
            return f"(force {self.formula(rest[0], s)} (\\{x}. {self.formula(rest[1], x)}))"
        if op == 8:
            x, s2 = self.fresh("x"), self.fresh()
            return (f"(force {self.formula(rest[0], s)} (\\{x}. ((\\{s2}. {self.formula(rest[1], s2)}) "
                    f"(Cell {x} {s}))))")
        if op == 9:
            ax, c = rest
            core = self.fresh("c")
            return (f"(force {self.formula(c, s)} (\\{core}. (app {self.axis(ax, core)} {core})))")
        if op == 10:
            (ax, c), d = rest
            v, t = self.fresh("v"), self.fresh("t")
            return (f"(force {self.formula(c, s)} (\\{v}. (force {self.formula(d, s)} "
                    f"(\\{t}. {self.edit(ax, v, t)}))))")
        if op == 11:
            hint, body = rest
            if N.is_cell(hint):
                h = self.fresh("h")
                return f"(force {self.formula(hint[1], s)} (\\{h}. {self.formula(body, s)}))"
            return self.formula(body, s)
        return "Err"


def program(formula: N.Noun, subject: N.Noun | None = None) -> str:
    """The SKIjack source: the library, `run s = …`, and `main := run subj`."""
    c = Compiler()
    src = [LIB, f"run s = {c.formula(formula, 's')}"]
    if subject is not None:
        src.append(f"subj := {c.lit(subject)}")
        src.append("main := run subj")
    return "\n".join(src) + "\n"
