"""Run a compiled program on Avon and read its product from the normal form.

`avon reduce` reduces to full normal form and leaves unknown words as inert
atoms.  So the product is read by applying a *show* term, written here by
bracket abstraction over free atoms, that rebuilds the noun as a first-order
term over `matom`, `mcell`, `merr`, `mnil`, `mcons`, `mt`, `mf`; the normal
form of `show main` is parsed back into a noun.  Avon's share strategy is the
default; `strategy="copy"` gives aviary's counts.
"""
from __future__ import annotations
import os, subprocess
from aviary_kernel.terms import pretty
from . import nock as N

AVON = os.environ.get("AVON", os.path.expanduser("~/avon/build/avon"))


# ---- a tiny bracket abstractor over text terms with free atoms
def _free(x, t):
    return any(_free(x, u) for u in t) if isinstance(t, tuple) else t == x


def _abs(x, m):
    if m == x:
        return "I"
    if not _free(x, m):
        return ("K", m)
    f, a = m
    if a == x and not _free(x, f):
        return f
    return (("S", _abs(x, f)), _abs(x, a))


def _lam(xs, body):
    for x in reversed(xs):
        body = _abs(x, body)
    return body


def _app(*xs):
    t = xs[0]
    for x in xs[1:]:
        t = (t, x)
    return t


def _show(t):
    if isinstance(t, tuple):
        f, a = t
        sa = _show(a)
        if isinstance(a, tuple):
            sa = "(" + sa + ")"
        return _show(f) + " " + sa
    return t


# Turing's fixed point
_A = _lam(["x", "y"], _app("y", _app("x", "x", "y")))
_THETA = (_A, _A)
# showbits = Θ (λr b. b mnil (λx s. mcons (x mt mf) (r s)))
_SHOWBITS = (_THETA, _lam(["r", "b"], _app("b", "mnil", _lam(["x", "s"], _app("mcons", _app("x", "mt", "mf"), _app("r", "s"))))))
# show = Θ (λr n. n (λb. matom (showbits b)) (λh t. mcell (r h) (r t)) (λh t c. mcell (r h) (r t)) merr)
_SHOW = (_THETA, _lam(["r", "n"], _app("n",
                                       _lam(["b"], _app("matom", (_SHOWBITS, "b"))),
                                       _lam(["h", "t"], _app("mcell", _app("r", "h"), _app("r", "t"))),
                                       _lam(["h", "t", "c"], _app("mcell", _app("r", "h"), _app("r", "t"))),
                                       "merr")))
SHOW_TEXT = _show(_SHOW)


def term_text(main) -> str:
    """The printed form (unfolds sharing; large)."""
    return "(" + SHOW_TEXT + ") (" + pretty(main) + ")"


def dag_text(main) -> str:
    """Avon's `dag` form: every distinct node once, `id=l.r` for an application,
    the leaves `S K I` and atom names, the root last.  Nodes are interned by
    identity for the reducer's term (which is a DAG already) and by structure
    for the show prefix."""
    from aviary_kernel.terms import App as _App
    ids: dict = {}
    lines: list[str] = []

    def node(key, rhs):
        if key in ids:
            return ids[key]
        i = len(lines)
        ids[key] = i
        lines.append(f"{i}={rhs}")
        return i

    def of_text(t):                       # the show term, a tuple tree
        if isinstance(t, tuple):
            return node(("t", t), f"{of_text(t[0])}.{of_text(t[1])}")
        return node(("a", t), t)

    def of_term(t):                       # aviary term, by identity, iterative post-order
        stack = [(t, False)]
        while stack:
            x, expanded = stack.pop()
            if not isinstance(_App, type) or not isinstance(x, _App):
                continue
            k = ("i", id(x))
            if k in ids:
                continue
            if expanded:
                node(k, f"{of_term1(x.fn)}.{of_term1(x.arg)}")
            else:
                stack.append((x, True))
                stack.append((x.arg, False))
                stack.append((x.fn, False))
        return of_term1(t)

    def of_term1(x):
        if isinstance(x, _App):
            return ids[("i", id(x))]
        return node(("a", x.name), x.name)

    root = node(("root",), f"{of_text(_SHOW)}.{of_term(main)}")
    return "dag " + " ".join(lines) + f" @{root}"


def _parse_nf(text: str) -> N.Noun:
    toks = text.replace("(", " ( ").replace(")", " ) ").split()
    pos = 0

    def expr():
        nonlocal pos
        items = []
        while pos < len(toks) and toks[pos] != ")":
            if toks[pos] == "(":
                pos += 1
                items.append(expr())
                pos += 1
            else:
                items.append(toks[pos]); pos += 1
        return items

    def noun(e):
        if isinstance(e, str):
            e = [e]
        h = e[0]
        if h == "matom":
            return bits(e[1])
        if h == "mcell":
            return (noun(e[1]), noun(e[2]))
        if h == "merr":
            raise N.Crash("product is Err")
        raise ValueError("not a product: " + str(e)[:80])

    def bits(e):
        if isinstance(e, str):
            e = [e]
        out, k = 0, 0
        while e[0] != "mnil":
            if e[0] != "mcons":
                raise ValueError("not bits: " + str(e)[:80])
            x = e[1] if isinstance(e[1], str) else e[1][0]
            out |= (1 if x == "mt" else 0) << k
            k += 1
            e = e[2] if isinstance(e[2], list) else [e[2]]
        return out

    return noun(expr())


def run_avon(main, strategy: str = "share", fuel: int | None = None, path: str | None = None,
             discover: bool = False, dag: bool = True):
    """Returns (noun or None on crash, contractions, status line).  `discover`
    turns on Avon's generic constructor and data jets (`--discover --data`)."""
    txt = dag_text(main) if dag else term_text(main)
    if path:
        open(path, "w").write(txt + "\n")
    args = [AVON, "reduce", f"--strategy={strategy}", "--budget=50000000"]
    if fuel:
        args.append(f"--fuel={fuel}")
    if discover:
        args += ["--discover", "--data"]
    r = subprocess.run(args, input=txt + "\n", capture_output=True, text=True)
    if r.returncode != 0 and not r.stdout:
        raise RuntimeError(r.stderr.strip()[:200])
    lines = r.stdout.splitlines()
    status = lines[0]
    count = int(status.split()[-1])
    body = " ".join(lines[1:])
    try:
        return _parse_nf(body), count, status
    except N.Crash:
        return None, count, status
