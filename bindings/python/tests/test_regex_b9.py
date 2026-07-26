# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# B-9: regular-expression / sequence constructor surface.
#
# Exercises ayz3's z3py-shaped regex API — Re/to_re, InRe, Star, Plus, Option,
# Union, Intersect, Complement, Range, Loop, Full, Empty, AllChar, and Concat
# over regexes — through AY's real solver and cross-checks it against z3py.
#
# SOUNDNESS CONTRACT (the whole point of this suite): every membership verdict
# ayz3 DECIDES (sat/unsat) must equal z3py's. Where AY's regex/sequence decision
# procedure is incomplete it may return a sound `unknown` — that is accepted
# here — but a WRONG sat/unsat (disagreeing with z3py) is a hard failure.
#
# The RE-term `sexpr()` is also checked for exact equality with z3py's, so the
# constructed terms are the same terms, not merely equi-satisfiable ones.

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False

requires_z3py = pytest.mark.usefixtures("required_reference_z3")


def fresh_solver():
    """A Solver with its own isolated Context (own assertion stack)."""
    return z.Solver(z.Context())


# ---------------------------------------------------------------------------
# Verdict helpers
# ---------------------------------------------------------------------------

def _ay_verdict(build):
    """Verdict of asserting `build(z)` (a single constraint) in a fresh solver."""
    s = fresh_solver()
    with s.using():
        s.add(build(z))
    return str(s.check())


def _z3_verdict(build):
    s = _z3.Solver()
    s.add(build(_z3))
    return str(s.check())


def _assert_parity(build):
    """ayz3 must agree with z3py where it decides; `unknown` is a sound pass."""
    zz = _z3_verdict(build)
    ay = _ay_verdict(build)
    assert ay in (zz, "unknown"), (
        f"regex verdict mismatch: z3py={zz} ayz3={ay} "
        "(a wrong sat/unsat is disqualifying)"
    )
    return zz, ay


# ---------------------------------------------------------------------------
# Membership builders (identical source runs against both `z` and `_z3`)
# ---------------------------------------------------------------------------

def _range_sat(m):
    s = m.String("s")
    return m.And(m.InRe(s, m.Range("a", "z")), s == "m")


def _range_unsat(m):
    s = m.String("s")
    return m.And(m.InRe(s, m.Range("a", "z")), s == "5")


def _loop_sat(m):
    s = m.String("s")
    return m.And(m.InRe(s, m.Loop(m.Re("x"), 2, 3)), s == "xx")


def _loop_len_unsat(m):
    # x{2,3} has length in [2,3]; forcing length 1 is unsat. (A length window is
    # AY's decidable handle for a bounded-loop membership.)
    s = m.String("s")
    return m.And(m.InRe(s, m.Loop(m.Re("x"), 2, 3)), m.Length(s) == 1)


def _union_sat(m):
    s = m.String("s")
    return m.And(m.InRe(s, m.Union(m.Re("ab"), m.Re("cd"))), s == "cd")


def _union_unsat(m):
    s = m.String("s")
    return m.And(m.InRe(s, m.Union(m.Re("ab"), m.Re("cd"))), s == "ef")


# ---------------------------------------------------------------------------
# Acceptance cases named in the task
# ---------------------------------------------------------------------------

@requires_z3py
def test_range_membership_parity():
    zz, _ = _assert_parity(_range_sat)
    assert zz == "sat"
    zz, _ = _assert_parity(_range_unsat)
    assert zz == "unsat"


# ---------------------------------------------------------------------------
# re.range EMPTY-LANGUAGE cases (SOUNDNESS regression guard).
#
# Per SMT-LIB / z3, (re.range lo hi) is the EMPTY language whenever an endpoint
# is not a single character (length != 1) or lo > hi. A membership over a
# nonempty witness is then UNSAT. AY previously looked only at the first
# character of each endpoint and returned a WRONG `sat` (the B-9 bug); these
# pin the fix against z3py.
# ---------------------------------------------------------------------------

# (build, z3py-expected-verdict) — every one must be DECIDED (not unknown) and
# must equal z3py's verdict.
_EMPTY_RANGE_CASES = [
    # Multi-char endpoints — the original wrong-`sat` repro.
    (lambda m: m.And(m.InRe(m.String("s"), m.Range("ab", "cd")), m.String("s") == "b"), "unsat"),
    (lambda m: m.And(m.InRe(m.String("s"), m.Range("ab", "cd")), m.String("s") == "a"), "unsat"),
    # One bad endpoint.
    (lambda m: m.And(m.InRe(m.String("s"), m.Range("ab", "x")), m.String("s") == "a"), "unsat"),
    # Empty endpoint(s).
    (lambda m: m.And(m.InRe(m.String("s"), m.Range("", "a")), m.String("s") == "a"), "unsat"),
    (lambda m: m.And(m.InRe(m.String("s"), m.Range("a", "")), m.String("s") == "a"), "unsat"),
    # Reversed single-char range (lo > hi).
    (lambda m: m.And(m.InRe(m.String("s"), m.Range("z", "a")), m.String("s") == "m"), "unsat"),
    # Empty language with a FREE witness — AY decides UNSAT via the empty
    # accepted-length set (no concrete value needed).
    (lambda m: m.InRe(m.String("s"), m.Range("ab", "cd")), "unsat"),
    (lambda m: m.InRe(m.String("s"), m.Range("z", "a")), "unsat"),
    # Single-char range that DOES contain the witness (fix must not over-refute).
    (lambda m: m.And(m.InRe(m.String("s"), m.Range("a", "z")), m.String("s") == "m"), "sat"),
    (lambda m: m.And(m.InRe(m.String("s"), m.Range("a", "z")), m.String("s") == "0"), "unsat"),
]


@requires_z3py
@pytest.mark.parametrize("build,expected", _EMPTY_RANGE_CASES)
def test_range_empty_language_parity(build, expected):
    zz, ay = _assert_parity(build)
    assert zz == expected, f"z3py oracle unexpected: {zz} != {expected}"
    # These range cases must be DECIDED by AY (no wrong verdict AND no unknown).
    assert ay == expected, f"AY must decide this range case: got {ay}, want {expected}"


def test_range_empty_language_decided_without_z3py():
    # The wrong-`sat` repro pinned WITHOUT z3py, so the core verdict is guarded
    # even when z3py is unavailable.
    s = fresh_solver()
    with s.using():
        s.add(z.InRe(z.String("s"), z.Range("ab", "cd")), z.String("s") == "b")
    assert s.check() == z.unsat


def test_range_repro_cross_context():
    # The task's EXACT repro form: terms built in the default context, added to a
    # solver with its OWN context (exercises the cross-context AST rebuild of the
    # B-9 regex operators). Must be unsat, matching z3py.
    s = z.String("s")
    sv = z.Solver()
    sv.add(z.InRe(s, z.Range("ab", "cd")))
    sv.add(s == "b")
    assert sv.check() == z.unsat


@requires_z3py
def test_loop_membership_parity():
    zz, _ = _assert_parity(_loop_sat)
    assert zz == "sat"
    zz, _ = _assert_parity(_loop_len_unsat)
    assert zz == "unsat"


@requires_z3py
def test_union_membership_parity():
    zz, _ = _assert_parity(_union_sat)
    assert zz == "sat"
    zz, _ = _assert_parity(_union_unsat)
    assert zz == "unsat"


# ---------------------------------------------------------------------------
# Star / Plus / Option / Complement / Intersect / Concat / Full / Empty /
# AllChar — membership decided == z3py (or sound unknown).
# ---------------------------------------------------------------------------

@requires_z3py
@pytest.mark.parametrize(
    "build",
    [
        # Star
        lambda m: m.And(m.InRe(m.String("s"), m.Star(m.Re("a"))), m.String("s") == "aaa"),
        lambda m: m.And(m.InRe(m.String("s"), m.Star(m.Re("a"))), m.String("s") == ""),
        lambda m: m.And(m.InRe(m.String("s"), m.Star(m.Re("a"))), m.String("s") == "ab"),
        # Plus
        lambda m: m.And(m.InRe(m.String("s"), m.Plus(m.Re("a"))), m.String("s") == "aa"),
        lambda m: m.And(m.InRe(m.String("s"), m.Plus(m.Re("a"))), m.String("s") == ""),
        # Option
        lambda m: m.And(m.InRe(m.String("s"), m.Option(m.Re("a"))), m.String("s") == ""),
        lambda m: m.And(m.InRe(m.String("s"), m.Option(m.Re("a"))), m.String("s") == "a"),
        lambda m: m.And(m.InRe(m.String("s"), m.Option(m.Re("a"))), m.String("s") == "aa"),
        # Complement
        lambda m: m.And(m.InRe(m.String("s"), m.Complement(m.Re("a"))), m.String("s") == "b"),
        lambda m: m.And(m.InRe(m.String("s"), m.Complement(m.Re("a"))), m.String("s") == "a"),
        # Intersect
        lambda m: m.And(
            m.InRe(m.String("s"), m.Intersect(m.Range("a", "z"), m.Re("a"))),
            m.String("s") == "a",
        ),
        lambda m: m.And(
            m.InRe(m.String("s"), m.Intersect(m.Range("a", "z"), m.Re("a"))),
            m.String("s") == "b",
        ),
        # Concat over regexes  (a b*)
        lambda m: m.And(
            m.InRe(m.String("s"), m.Concat(m.Re("a"), m.Star(m.Re("b")))),
            m.String("s") == "abbb",
        ),
        lambda m: m.And(
            m.InRe(m.String("s"), m.Concat(m.Re("a"), m.Star(m.Re("b")))),
            m.String("s") == "ba",
        ),
        # Full / Empty / AllChar
        lambda m: m.And(
            m.InRe(m.String("s"), m.Full(m.ReSort(m.StringSort()))),
            m.String("s") == "whatever",
        ),
        lambda m: m.And(
            m.InRe(m.String("s"), m.Empty(m.ReSort(m.StringSort()))),
            m.String("s") == "x",
        ),
        lambda m: m.And(
            m.InRe(m.String("s"), m.AllChar(m.ReSort(m.StringSort()))),
            m.String("s") == "a",
        ),
        lambda m: m.And(
            m.InRe(m.String("s"), m.AllChar(m.ReSort(m.StringSort()))),
            m.String("s") == "ab",
        ),
    ],
)
def test_regex_membership_parity(build):
    _assert_parity(build)


# ---------------------------------------------------------------------------
# sexpr parity: the constructed RE terms are the same terms z3py builds.
# ---------------------------------------------------------------------------

@requires_z3py
def test_regex_sexpr_matches_z3py():
    s = fresh_solver()
    with s.using():
        ay = {
            "to_re": z.Re("a"),
            "star": z.Star(z.Re("a")),
            "plus": z.Plus(z.Re("a")),
            "option": z.Option(z.Re("a")),
            "union": z.Union(z.Re("ab"), z.Re("cd")),
            "concat": z.Concat(z.Re("a"), z.Re("b")),
            "intersect": z.Intersect(z.Re("a"), z.Re("b")),
            "complement": z.Complement(z.Re("a")),
            "range": z.Range("a", "z"),
            "loop": z.Loop(z.Re("x"), 2, 3),
            "full": z.Full(z.ReSort(z.StringSort())),
            "empty": z.Empty(z.ReSort(z.StringSort())),
            "allchar": z.AllChar(z.ReSort(z.StringSort())),
            "in_re": z.InRe(z.String("s"), z.Range("a", "z")),
        }
    zp = {
        "to_re": _z3.Re("a"),
        "star": _z3.Star(_z3.Re("a")),
        "plus": _z3.Plus(_z3.Re("a")),
        "option": _z3.Option(_z3.Re("a")),
        "union": _z3.Union(_z3.Re("ab"), _z3.Re("cd")),
        "concat": _z3.Concat(_z3.Re("a"), _z3.Re("b")),
        "intersect": _z3.Intersect(_z3.Re("a"), _z3.Re("b")),
        "complement": _z3.Complement(_z3.Re("a")),
        "range": _z3.Range("a", "z"),
        "loop": _z3.Loop(_z3.Re("x"), 2, 3),
        "full": _z3.Full(_z3.ReSort(_z3.StringSort())),
        "empty": _z3.Empty(_z3.ReSort(_z3.StringSort())),
        "allchar": _z3.AllChar(_z3.ReSort(_z3.StringSort())),
        "in_re": _z3.InRe(_z3.String("s"), _z3.Range("a", "z")),
    }
    for k in ay:
        assert ay[k].sexpr() == zp[k].sexpr(), (
            f"{k}: ayz3 sexpr {ay[k].sexpr()!r} != z3py {zp[k].sexpr()!r}"
        )


# ---------------------------------------------------------------------------
# Structural / typing checks that do not need z3py.
# ---------------------------------------------------------------------------

def test_re_result_is_reref():
    s = fresh_solver()
    with s.using():
        r = z.Star(z.Re("a"))
        assert isinstance(r, z.ReRef)
        assert r.sort_ref.kind == "RegLan"
        # InRe yields a Bool.
        atom = z.InRe(z.String("s"), r)
        assert isinstance(atom, z.BoolRef)


def test_re_str_coercion():
    # A bare Python str is lifted to Re(str) by the regex builders.
    s = fresh_solver()
    with s.using():
        assert z.Star("a").sexpr() == z.Star(z.Re("a")).sexpr()
        assert z.Union("ab", "cd").sexpr() == z.Union(z.Re("ab"), z.Re("cd")).sexpr()


def test_reref_add_is_union():
    # z3py overloads `+` on regexes as union (and nothing else); mirror it.
    s = fresh_solver()
    with s.using():
        r = z.Re("a") + z.Re("b")
        assert isinstance(r, z.ReRef)
        assert r.sexpr() == z.Union(z.Re("a"), z.Re("b")).sexpr()
        with pytest.raises(TypeError):
            _ = z.Re("a") * z.Re("b")


def test_union_single_arg_identity():
    s = fresh_solver()
    with s.using():
        r = z.Re("a")
        assert z.Union(r) is r
        assert z.Intersect(r) is r


def test_empty_string_sort_is_empty_literal():
    # z3py: Empty(StringSort()) is the empty string "".
    s = fresh_solver()
    with s.using():
        e = z.Empty(z.StringSort())
        assert isinstance(e, z.SeqRef)
        assert e.as_string() == ""


def test_full_requires_regex_sort():
    with pytest.raises(z.AyZ3Exception):
        z.Full(z.StringSort())


def test_decided_membership_examples():
    # A couple of fully-decided cases pinned WITHOUT z3py, so the suite still
    # guards the core verdicts when z3py is absent.
    s = fresh_solver()
    with s.using():
        s.add(z.InRe(z.String("s"), z.Range("a", "z")), z.String("s") == "m")
    assert s.check() == z.sat

    s = fresh_solver()
    with s.using():
        s.add(z.InRe(z.String("s"), z.Union(z.Re("ab"), z.Re("cd"))), z.String("s") == "ef")
    assert s.check() == z.unsat
