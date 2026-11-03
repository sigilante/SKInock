"""Compiler conformance: urbit/benchmark's reference tests, crash and race
cases, and agreement between aviary and Avon."""
import json, os, shutil, pytest
from skinock import nock as N
from skinock.run import Program, run

NORM = os.path.expanduser("~/Code/urbit/benchmark/norm/tests.json")
TESTS = json.load(open(NORM)) if os.path.exists(NORM) else []


@pytest.mark.parametrize("e", TESTS, ids=[f"{i}-op{e['opcode']}" for i, e in enumerate(TESTS)])
def test_norm(e):
    s, f = N.parse(e["subject"]), N.parse(e["formula"])
    want = None if e["result"] is None else N.parse(e["result"])
    assert run(f, s).value == want


@pytest.mark.parametrize("e", TESTS, ids=[f"{i}-op{e['opcode']}" for i, e in enumerate(TESTS)])
def test_norm_as_data(e):
    # the formula supplied as data at run time: subject [s f], formula [2 [0 2] [0 3]],
    # the literal encoded without code so a plain Cell reaches opcode 2 and nockI interprets
    s, f = N.parse(e["subject"]), N.parse(e["formula"])
    want = None if e["result"] is None else N.parse(e["result"])
    assert run(N.parse("[2 [0 2] [0 3]]"), (s, f), code=False).value == want


def test_python_oracle_matches_norm():
    for e in TESTS:
        s, f = N.parse(e["subject"]), N.parse(e["formula"])
        want = None if e["result"] is None else N.parse(e["result"])
        try:
            got = N.nock(s, f)
        except N.Crash:
            got = None
        assert got == want, e["description"]


def test_count_up_dec():
    f = N.parse("[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]")
    assert run(f, 7).value == 6
    assert run(f, 1).value == 0


def test_count_up_dec_interpreted():
    f = N.parse("[8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]")
    assert run(f, 5, code=False).value == 4          # the battery is a plain Cell: 9 2 goes to nockI
    assert run(N.parse("[2 [0 2] [0 3]]"), (5, f), code=False).value == 4
    assert run(N.parse("[2 [0 2] [0 3]]"), (5, f)).value == 4    # as data, but a Form: the fast path


def test_dynamic_formula_assembled_by_autocons():
    # [[1 4] [1 0] [1 1]] builds [4 0 1] at run time; no literal carries code for it
    assert run(N.parse("[2 [0 1] [[1 4] [1 0] [1 1]]]"), 42).value == 43
    # a dynamic axis beyond one bit: [0 7] against [[1 2] [3 4]]
    assert run(N.parse("[2 [1 [[1 2] [3 4]]] [[1 0] [1 7]]]"), 0).value == 4
    assert run(N.parse("[2 [1 [[1 2] [3 4]]] [[1 0] [1 6]]]"), 0).value == 3
    assert run(N.parse("[2 [1 [[1 2] [3 4]]] [[1 0] [1 0]]]"), 0).value is None
    assert run(N.parse("[2 [1 [[1 2] [3 4]]] [[1 0] [1 8]]]"), 0).value is None   # into an atom
    # a dynamic edit beyond one bit, and an opcode outside 0..11
    assert run(N.parse("[2 [1 [[1 2] [3 4]]] [[1 10] [[1 6] [1 1] [1 99]] [1 0] [1 1]]]"), 0).value == N.parse("[[1 2] 99 4]")
    assert run(N.parse("[2 [1 0] [[1 12] [1 0] [1 0]]]"), 0).value is None


def test_interpreter_strictness_matches_compiled():
    data = N.parse("[2 [0 2] [0 3]]")
    for f, s, want in [("[7 [0 0] [1 42]]", 1, None), ("[8 [0 0] [1 42]]", 1, None),
                       ("[[0 0] [1 1]]", 1, None), ("[6 [1 0] [1 1] [0 0]]", 1, 1),
                       ("[11 [7 [0 0]] [1 5]]", 0, None), ("[11 7 [1 5]]", 0, 5)]:
        assert run(data, (s, N.parse(f)), code=False).value == want
    dec0 = "[7 [1 0] 8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]"
    assert run(data, (1, N.parse(f"[[0 0] {dec0}]")), max_steps=200_000, code=False).value is None


def test_edit_crash_under_path_is_not_hidden_in_a_field():
    # #[4 99 [1 2]] crashes; the product must not be a Cell with Err inside
    for code in (True, False):
        for f, want in [("[10 [4 [1 99]] [0 1]]", None),
                        ("[5 [10 [4 [1 99]] [0 1]] [10 [4 [1 99]] [0 1]]]", None),
                        ("[3 [10 [4 [1 99]] [0 1]]]", None)]:
            assert run(N.parse(f), N.parse("[1 2]"), code=code).value == want
            assert run(N.parse("[2 [0 2] [0 3]]"), (N.parse("[1 2]"), N.parse(f)), code=code).value == want


def test_strictness_a_crash_in_a_discarded_operand_still_crashes():
    # Nock evaluates [0 0] before 7 runs its second formula; a lazy embedding would return 42.
    assert run(N.parse("[7 [0 0] [1 42]]"), 1).value is None
    assert run(N.parse("[8 [0 0] [1 42]]"), 1).value is None
    assert run(N.parse("[[0 0] [1 1]]"), 1).value is None
    # the unchosen branch of 6 is never evaluated
    assert run(N.parse("[6 [1 0] [1 1] [0 0]]"), 1).value == 1


def test_race_head_crash_before_tail_diverges_is_a_crash():
    # autocons: head crashes, tail is the count-up dec of 0, which diverges;
    # Vere's order evaluates the head first, so the outcome is a crash.
    dec0 = "[7 [1 0] 8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]"
    assert run(N.parse(f"[[0 0] {dec0}]"), 1, max_steps=200_000).value is None


def test_edit_mixed_path():
    assert run(N.parse("[10 [6 [1 99]] [0 1]]"), N.parse("[[1 2] [3 4]]")).value == N.parse("[[1 2] 99 4]")


@pytest.mark.skipif(not shutil.which(os.path.expanduser("~/avon/build/avon")), reason="no Avon")
def test_avon_agrees_with_aviary():
    from skinock.avon import run_avon
    for s, f in [("42", "[4 0 1]"), ("[1 2]", "[0 6]"), ("0", "[9 2 [1 [[4 0 3] 42]]]")]:
        p = Program(N.parse(f), N.parse(s))
        assert run_avon(p.main)[0] == p.run().value


def test_shape_crash_precedes_operand_evaluation():
    # lean-nock's Malformed is checked at a node before its operands run: a
    # 6 whose tail is an atom crashes even though its condition would diverge.
    dec0 = "[7 [1 0] 8 [1 0] 8 [1 6 [5 [0 7] 4 0 6] [0 6] 9 2 [0 2] [4 0 6] 0 7] 9 2 0 1]"
    bad = N.parse(f"[6 {dec0} 99]")
    assert N.malformed(bad)
    assert run(bad, 1, max_steps=200_000).value is None                 # compiled
    assert run(N.parse("[2 [0 2] [0 3]]"), (1, bad), max_steps=200_000, code=False).value is None  # interpreted


def test_op10_evaluates_the_target_before_the_patch():
    # lean-nock (NockEval.op10, Order.lean) and Vere evaluate d before c in
    # [10 [b c] d]; here d diverges and c crashes, so the outcome is divergence.
    s = N.parse("[2 [0 1] [0 1]]")
    f = N.parse("[10 [2 [0 0]] [2 [0 1] [0 1]]]")
    with pytest.raises(N.Fuel):
        N.nock(s, f, fuel=2000)
    from skinock.run import SkiFuel
    with pytest.raises(SkiFuel):
        run(f, s, max_steps=100_000)
    with pytest.raises(SkiFuel):
        run(N.parse("[2 [0 2] [0 3]]"), (s, f), max_steps=100_000, code=False)
    # and the patch is still evaluated: a crashing patch over a good tree crashes
    assert run(N.parse("[10 [2 [0 0]] [0 1]]"), s).value is None
