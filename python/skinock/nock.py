"""Nock 4K: nouns, text, and a reference evaluator in Vere's order.

Nouns are Python ints (atoms) and 2-tuples (cells).  The evaluator raises
`Crash` on a deterministic crash and `Fuel` when its step budget runs out;
it evaluates in the order lean-nock discharged against Vere: autocons head
then tail, opcode 2 subject then formula, opcode 5 left then right,
opcode 10 the target tree then the patch, a dynamic hint before its body.
"""
from __future__ import annotations

Noun = int | tuple


class Crash(Exception):
    pass


class Fuel(Exception):
    pass


# ---------------------------------------------------------------- text

def parse(s: str) -> Noun:
    """Parse `[a b c]` notation, right-nested; digits may carry dots."""
    toks = s.replace("[", " [ ").replace("]", " ] ").split()
    pos = 0

    def item():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t == "[":
            xs = []
            while toks[pos] != "]":
                xs.append(item())
            pos += 1
            if len(xs) < 2:
                raise ValueError("a cell needs two parts")
            n = xs[-1]
            for x in reversed(xs[:-1]):
                n = (x, n)
            return n
        if t == "]":
            raise ValueError("unexpected ]")
        return int(t.replace(".", ""))

    n = item()
    if pos != len(toks):
        raise ValueError("trailing input")
    return n


def show(n: Noun) -> str:
    if isinstance(n, int):
        return str(n)
    parts = []
    while isinstance(n, tuple):
        parts.append(show(n[0]))
        n = n[1]
    parts.append(str(n))
    return "[" + " ".join(parts) + "]"


def is_cell(n: Noun) -> bool:
    return isinstance(n, tuple)


# ---------------------------------------------------------------- formulas

def is_formula(n: Noun) -> bool:
    """Does `n` parse as a Nock 4K formula?  (Autocons: both halves formulas.)"""
    if not is_cell(n):
        return False
    op, rest = n
    if is_cell(op):
        return is_formula(op) and is_formula(rest)
    if op == 0:
        return isinstance(rest, int)
    if op == 1:
        return True
    if op in (3, 4):
        return is_formula(rest)
    if op in (2, 5, 7, 8):
        return is_cell(rest) and is_formula(rest[0]) and is_formula(rest[1])
    if op == 6:
        return (is_cell(rest) and is_cell(rest[1]) and is_formula(rest[0])
                and is_formula(rest[1][0]) and is_formula(rest[1][1]))
    if op == 9:
        return is_cell(rest) and isinstance(rest[0], int) and is_formula(rest[1])
    if op == 10:
        return (is_cell(rest) and is_cell(rest[0]) and isinstance(rest[0][0], int)
                and is_formula(rest[0][1]) and is_formula(rest[1]))
    if op == 11:
        if not is_cell(rest):
            return False
        hint, body = rest
        if is_cell(hint):
            return isinstance(hint[0], int) and is_formula(hint[1]) and is_formula(body)
        return is_formula(body)
    if op == 12:
        return is_cell(rest) and is_formula(rest[0]) and is_formula(rest[1])
    return False


# ---------------------------------------------------------------- evaluator

def malformed(f: Noun, scry: bool = False) -> bool:
    """lean-nock's `Malformed`: the shallow shape check a node makes before
    evaluating its operands.  With `scry`, `[12 ref path]` is well formed
    (the extension a resolver gives it)."""
    if not is_cell(f):
        return True
    op, t = f
    if is_cell(op):
        return False
    if op in (0, 1, 3, 4):
        return False
    if op in (2, 5, 7, 8, 9, 11):
        return not is_cell(t)
    if op == 6:
        return not (is_cell(t) and is_cell(t[1]))
    if op == 10:
        return not (is_cell(t) and is_cell(t[0]))
    if op == 12 and scry:
        return not is_cell(t)
    return True


def slot(axis: int, n: Noun) -> Noun:
    if axis == 0:
        raise Crash("axis 0")
    if axis == 1:
        return n
    path = bin(axis)[3:]
    for b in path:
        if not is_cell(n):
            raise Crash("slot into atom")
        n = n[0] if b == "0" else n[1]
    return n


def edit(axis: int, v: Noun, t: Noun) -> Noun:
    """`#[axis v t]`: `t` with the subtree at `axis` replaced by `v`."""
    if axis == 0:
        raise Crash("edit axis 0")
    path = bin(axis)[3:]

    def go(i: int, cur: Noun) -> Noun:
        if i == len(path):
            return v
        if not is_cell(cur):
            raise Crash("edit into atom")
        if path[i] == "0":
            return (go(i + 1, cur[0]), cur[1])
        return (cur[0], go(i + 1, cur[1]))
    return go(0, t)


class Evaluator:
    """`resolver`: None (opcode 12 crashes) or a dict {(ref, path): value}."""

    def __init__(self, fuel: int | None = None, resolver: dict | None = None):
        self.steps = 0
        self.fuel = fuel
        self.resolver = resolver

    def tick(self):
        self.steps += 1
        if self.fuel is not None and self.steps > self.fuel:
            raise Fuel()

    def nock(self, s: Noun, f: Noun) -> Noun:
        try:
            return self._nock(s, f)
        except (TypeError, IndexError, ValueError):
            raise Crash("malformed formula")
        except RecursionError:
            raise Fuel("recursion depth")

    def _nock(self, s: Noun, f: Noun) -> Noun:
        self.tick()
        if malformed(f, scry=self.resolver is not None):
            raise Crash("malformed formula")
        op, rest = f
        if is_cell(op):
            h = self.nock(s, op)
            t = self.nock(s, rest)
            return (h, t)
        if op == 0:
            if not isinstance(rest, int):
                raise Crash("axis")
            return slot(rest, s)
        if op == 1:
            return rest
        if op == 2:
            s2 = self.nock(s, rest[0])
            f2 = self.nock(s, rest[1])
            return self.nock(s2, f2)
        if op == 3:
            return 0 if is_cell(self.nock(s, rest)) else 1
        if op == 4:
            v = self.nock(s, rest)
            if is_cell(v):
                raise Crash("increment a cell")
            return v + 1
        if op == 5:
            a = self.nock(s, rest[0])
            b = self.nock(s, rest[1])
            return 0 if a == b else 1
        if op == 6:
            c = self.nock(s, rest[0])
            if c == 0:
                return self.nock(s, rest[1][0])
            if c == 1:
                return self.nock(s, rest[1][1])
            raise Crash("non-loobean condition")
        if op == 7:
            return self.nock(self.nock(s, rest[0]), rest[1])
        if op == 8:
            return self.nock((self.nock(s, rest[0]), s), rest[1])
        if op == 9:
            core = self.nock(s, rest[1])
            return self.nock(core, slot(rest[0], core))
        if op == 10:
            (axis, c), d = rest
            t = self.nock(s, d)
            v = self.nock(s, c)
            return edit(axis, v, t)
        if op == 11:
            hint, body = rest
            if is_cell(hint):
                self.nock(s, hint[1])
            return self.nock(s, body)
        if op == 12:
            ref = self.nock(s, rest[0])
            path = self.nock(s, rest[1])
            if (ref, path) in self.resolver:
                return self.resolver[(ref, path)]
            raise Crash("scry miss")
        raise Crash(f"opcode {op}")


def nock(s: Noun, f: Noun, fuel: int | None = None, resolver: dict | None = None) -> Noun:
    return Evaluator(fuel, resolver).nock(s, f)
