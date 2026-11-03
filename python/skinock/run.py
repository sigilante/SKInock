"""Compile a Nock program to a closed SKI term, run it, and read the product.

The product is read behaviourally: the term is applied to four fresh marker
atoms (one per constructor of `noun`) and reduced to weak head normal form;
the marker that comes back says which constructor it is, and its arguments
are read the same way.  Reading forces the whole noun, as Nock's product is
a whole noun; a crash anywhere in it is the `Err` marker.
"""
from __future__ import annotations
from dataclasses import dataclass
import skijack
from skijack.probe import fast_reduce
from aviary_kernel.terms import Atom, App, spine
from aviary_kernel.reduce import Status
from . import nock as N
from .compile import program


class SkiCrash(Exception):
    pass


class SkiFuel(Exception):
    pass


@dataclass
class Result:
    value: N.Noun | None      # None on crash
    steps: int                # host contractions, the run and the read-out together
    atoms: int                # size of the compiled `main` term


class Program:
    """A compiled Nock formula, reusable over subjects."""

    def __init__(self, formula: N.Noun, subject: N.Noun, code: bool = True):
        self.src = program(formula, subject, code)
        self.exp = skijack.compile(self.src, check=False, generate_forms=False)
        self.env = self.exp.env
        self.main = self.exp.terms["main"]
        self.atoms = self.exp.sizes["main"]

    def run(self, max_steps: int = 5_000_000) -> Result:
        steps = 0
        MA, MC, MF, ME = Atom("MAtom"), Atom("MCell"), Atom("MForm"), Atom("MErr")
        BN, BC, BT, BF = Atom("MNil"), Atom("MCons"), Atom("MT"), Atom("MF")

        def whnf(t):
            nonlocal steps
            r = fast_reduce(t, self.env, whnf_only=True, max_steps=max_steps - steps)
            steps += r.steps
            if r.status is Status.FUEL:
                raise SkiFuel()
            return r.term

        def head_args(t):
            h, args = spine(t)
            return h, list(args)

        def read_bit(t):
            h, _ = head_args(whnf(App(App(t, BT), BF)))
            return 1 if h == BT else 0

        def read_bits(t):
            out, k = 0, 0
            while True:
                h, args = head_args(whnf(App(App(t, BN), BC)))
                if h == BN:
                    return out
                b, rest = args
                out |= read_bit(b) << k
                k += 1
                t = rest

        def read(t):
            h, args = head_args(whnf(App(App(App(App(t, MA), MC), MF), ME)))
            if h == MA:
                return read_bits(args[0])
            if h in (MC, MF):
                return (read(args[0]), read(args[1]))
            if h == ME:
                raise SkiCrash()
            raise ValueError(f"not a noun: {h}")

        try:
            v = read(self.main)
        except SkiCrash:
            return Result(None, steps, self.atoms)
        return Result(v, steps, self.atoms)


def run(formula: N.Noun, subject: N.Noun, max_steps: int = 5_000_000, code: bool = True) -> Result:
    return Program(formula, subject, code).run(max_steps)
