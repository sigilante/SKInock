"""Nock formulas to SKIjack source, and on to closed SKI terms.

The compiled formula is an expression over a subject variable.  Strictness
follows Nock: both halves of an autocons, both operands of opcodes 2 and 5, the
target then the patch of 10, the pushed value of 8, the subject of 7 and 9 and the hint of a dynamic
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
    """Emits SKIjack source.  Literals are hash-consed into named definitions
    (`litN := …`) and a literal formula's code into a named equation
    (`codeN s = …`), so every distinct sub-noun and every formula body is
    emitted once and shared in the term."""

    def __init__(self, code: bool = True, scry: bool = False):
        self.scry = scry
        self.k = 0
        self.code = code          # False: a literal formula is a plain Cell, never a Form
        self.memo: dict = {}      # noun -> name
        self.defs: list[str] = []

    def fresh(self, base="s"):
        self.k += 1
        return f"{base}{self.k}"

    # ---- literals
    def lit(self, n: N.Noun) -> str:
        if isinstance(n, int) and n < 2:
            return f"(Atom {bits(n)})"
        if n in self.memo:
            return self.memo[n]
        name = self.fresh("lit")
        self.memo[n] = name
        if isinstance(n, int):
            self.defs.append(f"{name} := Atom {bits(n)}")
        else:
            h, t = self.lit(n[0]), self.lit(n[1])
            if self.code and N.is_formula(n):
                code = self.fresh("code")
                s = self.fresh()
                self.defs.append(f"{code} {s} = {self.formula(n, s)}")
                self.defs.append(f"{name} := Form {h} {t} {code}")
            else:
                self.defs.append(f"{name} := Cell {h} {t}")
        return name

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
            # the rebuilt subtree is forced before the Cell is built, so a
            # crash under the path cannot hide in a field of the product
            i_ = self.fresh("i")
            if path[i] == "0":
                inner = go(i + 1, h)
                return (f"(force (hd {cur}) (\\{h}. (force (tl {cur}) (\\{tl_}. "
                        f"(force {inner} (\\{i_}. (Cell {i_} {tl_})))))))")
            inner = go(i + 1, tl_)
            return (f"(force (hd {cur}) (\\{h}. (force (tl {cur}) (\\{tl_}. "
                    f"(force {inner} (\\{i_}. (Cell {h} {i_})))))))")
        return go(0, t)

    # ---- formulas
    def formula(self, f: N.Noun, s: str) -> str:
        if N.malformed(f, scry=self.scry):
            return "Err"
        op, rest = f
        if op == 12:
            x, p = self.fresh("x"), self.fresh("p")
            return (f"(force {self.formula(rest[0], s)} (\\{x}. (force {self.formula(rest[1], s)} "
                    f"(\\{p}. (scry {x} {p})))))")
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
            pull = f"(app {self.axis(ax, core)} {core})" if isinstance(ax, int) else "Err"
            return f"(force {self.formula(c, s)} (\\{core}. {pull}))"
        if op == 10:
            (ax, c), d = rest
            v, t = self.fresh("v"), self.fresh("t")
            ed = self.edit(ax, v, t) if isinstance(ax, int) else "Err"
            # lean-nock and Vere evaluate the target tree d before the patch c
            return (f"(force {self.formula(d, s)} (\\{t}. (force {self.formula(c, s)} "
                    f"(\\{v}. {ed}))))")
        if op == 11:
            hint, body = rest
            if N.is_cell(hint):
                h = self.fresh("h")
                return f"(force {self.formula(hint[1], s)} (\\{h}. {self.formula(body, s)}))"
            return self.formula(body, s)
        return "Err"


def scry_def(c: "Compiler", facts) -> str:
    """`scry x p = …`: a resolver over a fact table [((ref, path), value)…],
    compared structurally with `eq`; a miss is a crash (lean-nock's
    semantics for opcode 12, Vere's outside `+mock`)."""
    body = "Err"
    for (ref, path), value in reversed(list(facts or [])):
        body = (f"(ifn (eq x {c.lit(ref)}) (ifn (eq p {c.lit(path)}) {c.lit(value)} {body}) {body})")
    return f"scry x p = {body}"


def program(formula: N.Noun, subject: N.Noun | None = None, code: bool = True,
            scry=None) -> str:
    """The SKIjack source: the library, the resolver, `run s = …`, and
    `main := run subj`.  With `code=False` literal cells are plain `Cell`s
    (no `Form`), so a formula reaching opcode 2 or 9 from data is interpreted
    by `nockI`.  `scry` is None (opcode 12 crashes) or a fact table
    [((ref, path), value)…] that opcode 12 consults."""
    c = Compiler(code, scry=scry is not None)
    run = f"run s = {c.formula(formula, 's')}"
    sc = scry_def(c, scry)
    tail = []
    if subject is not None:
        tail.append(f"subj := {c.lit(subject)}")
        tail.append("main := run subj")
    return "\n".join([LIB, *c.defs, sc, run, *tail]) + "\n"
