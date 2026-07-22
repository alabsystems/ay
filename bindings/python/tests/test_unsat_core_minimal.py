# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Phase-6 MINIMAL UNSAT CORE tests for ayz3.
#
# ayz3.Solver.unsat_core() now returns a DELETION-MINIMAL (irredundant) unsat
# core via deletion-based minimization: starting from the subset the engine
# reports, each tracker is tentatively removed and the solver re-checked under
# the remaining trackers (as assumptions); a tracker is dropped permanently iff
# the remainder is still UNSAT. Iterated to a fixpoint, this yields a core where
# removing ANY single element makes the remainder SAT.
#
# SOUNDNESS / MINIMALITY checks:
#   * SOUND: re-checking ONLY the core's constraints (as hard asserts) in a
#     FRESH solver is UNSAT. The core is the authority — a non-core is never
#     returned.
#   * MINIMAL: dropping any single core element and re-checking the rest (as
#     hard asserts) is SAT. A non-minimal set is never claimed minimal.
#   * Every core element is one of the tracked literals (never fabricated).
#   * SIZE: the core is no larger than the full tracked set.
#   * CROSS-CHECK vs real z3py 4.15.4 (the oracle): verdicts agree; ayz3's core
#     size equals z3py's minimal core size. We do NOT assert exact set-equality
#     unless the minimal core is UNIQUE, because when several minimal cores
#     exist z3 and ayz3 may each pick a different (equally valid) one.
#
# Run:  cargo build -p ay-ffi   &&   pytest bindings/python/tests -v

import pytest

import ayz3 as z

try:
    import z3 as _z3
    HAVE_Z3PY = True
except Exception:  # pragma: no cover - depends on environment
    _z3 = None
    HAVE_Z3PY = False


def fresh_solver():
    """A Solver with its own isolated Context (independent assertion stack)."""
    return z.Solver(z.Context())


# ---------------------------------------------------------------------------
# Verification primitives (the soundness/minimality authority lives HERE — a
# fresh solve over just the core constraints, not a claim by the binding).
# ---------------------------------------------------------------------------

def _recheck_subset_is_unsat(names, builders):
    """Re-assert ONLY the named constraints (as hard asserts) in a fresh solver
    and return whether that subset is UNSAT."""
    s = fresh_solver()
    with s.using():
        for nm in names:
            assert nm in builders, f"core literal {nm!r} is not a tracked literal"
            s.add(builders[nm]())
    return s.check() == z.unsat


def _recheck_subset_is_sat(names, builders):
    s = fresh_solver()
    with s.using():
        for nm in names:
            assert nm in builders
            s.add(builders[nm]())
    return s.check() == z.sat


def _assert_sound_and_minimal(core, builders, full_tracked):
    """Assert `core` (a list of tracker consts) is: a subset of the tracked
    literals, a SOUND unsat subset, DELETION-MINIMAL, and no larger than the
    full tracked set. Returns the set of core names."""
    names = [c.decl_name for c in core]
    name_set = set(names)
    # (0) Subset of the tracked literals — never a fabricated literal.
    assert name_set.issubset(set(full_tracked)), (
        f"core {name_set} is not a subset of tracked {set(full_tracked)}"
    )
    assert len(names) == len(name_set), "core must not contain duplicates"
    # (1) Size: no larger than the full tracked set.
    assert len(name_set) <= len(full_tracked)
    # (2) SOUND: the core's constraints alone are UNSAT.
    assert _recheck_subset_is_unsat(names, builders), (
        f"core {name_set} is NOT a real unsat core (re-check was SAT)"
    )
    # (3) DELETION-MINIMAL: dropping any one element makes the rest SAT.
    for drop in range(len(names)):
        remaining = names[:drop] + names[drop + 1:]
        assert _recheck_subset_is_sat(remaining, builders), (
            f"core {name_set} is NOT deletion-minimal: dropping {names[drop]!r} "
            f"leaves {set(remaining)} which is still UNSAT"
        )
    return name_set


# ---------------------------------------------------------------------------
# Over-determined instances: only a SUBSET of the tracked asserts is the core.
# ---------------------------------------------------------------------------

def test_minimal_core_unique_among_many_redundant_trackers():
    # Eight tracked asserts; the ONLY conflict is x>10 ∧ x<0. The other six are
    # satisfiable distractors. The unique minimal core is exactly {hi, lo}.
    builders = {
        "hi": lambda: z.Int("x") > 10,
        "lo": lambda: z.Int("x") < 0,
        "d1": lambda: z.Int("y") > 0,
        "d2": lambda: z.Int("y") < 100,
        "d3": lambda: z.Int("z") == 5,
        "d4": lambda: z.Int("w") != 7,
        "d5": lambda: z.Bool("b1"),
        "d6": lambda: z.Or(z.Bool("b2"), z.Bool("b3")),
    }
    s = fresh_solver()
    with s.using():
        for nm, build in builders.items():
            s.assert_and_track(build(), z.Bool(nm))
    assert s.check() == z.unsat
    core = s.unsat_core()
    names = _assert_sound_and_minimal(core, builders, list(builders))
    # The conflict is unique → the minimal core is exactly {hi, lo}.
    assert names == {"hi", "lo"}


def test_minimal_core_three_way_mutually_unsat_subset():
    # Five trackers; the minimal conflict is the TRIPLE a+b+c with
    # a = (p), b = (q), c = (Not(And(p,q))) ... build an arithmetic triple:
    #   x == 1, y == 1, x + y == 3   (unsat as a triple; each pair is sat).
    # Two distractors are independently satisfiable.
    builders = {
        "x1": lambda: z.Int("x") == 1,
        "y1": lambda: z.Int("y") == 1,
        "sum3": lambda: z.Int("x") + z.Int("y") == 3,
        "d1": lambda: z.Int("k") > 0,
        "d2": lambda: z.Int("k") < 50,
    }
    s = fresh_solver()
    with s.using():
        for nm, build in builders.items():
            s.assert_and_track(build(), z.Bool(nm))
    assert s.check() == z.unsat
    core = s.unsat_core()
    names = _assert_sound_and_minimal(core, builders, list(builders))
    # All three of x1,y1,sum3 are required (any pair is satisfiable).
    assert names == {"x1", "y1", "sum3"}


def test_minimal_core_when_multiple_minimal_cores_exist():
    # x>5, x<3, x==4 : two distinct minimal cores {x>5,x<3} and {x<3,x==4}.
    # ayz3 must return ONE of them, and it must be sound + deletion-minimal of
    # size 2 (never the full set of 3).
    builders = {
        "gt5": lambda: z.Int("x") > 5,
        "lt3": lambda: z.Int("x") < 3,
        "eq4": lambda: z.Int("x") == 4,
    }
    s = fresh_solver()
    with s.using():
        for nm, build in builders.items():
            s.assert_and_track(build(), z.Bool(nm))
    assert s.check() == z.unsat
    core = s.unsat_core()
    names = _assert_sound_and_minimal(core, builders, list(builders))
    assert len(names) == 2
    assert names in ({"gt5", "lt3"}, {"lt3", "eq4"})


def test_minimal_core_pure_boolean_pigeonhole_like():
    # Pure-Boolean over-determined unsat: p, q, Not(p), plus distractors.
    # Minimal core is {p, np} (p and Not(p)).
    builders = {
        "p": lambda: z.Bool("p"),
        "q": lambda: z.Bool("q"),
        "np": lambda: z.Not(z.Bool("p")),
        "r": lambda: z.Or(z.Bool("r1"), z.Bool("r2")),
        "s": lambda: z.Implies(z.Bool("s1"), z.Bool("s2")),
    }
    s = fresh_solver()
    with s.using():
        for nm, build in builders.items():
            s.assert_and_track(build(), z.Bool(nm))
    assert s.check() == z.unsat
    core = s.unsat_core()
    names = _assert_sound_and_minimal(core, builders, list(builders))
    assert names == {"p", "np"}


def test_core_with_untracked_hard_assert_excludes_hard():
    # A HARD (untracked) assert participates in the conflict but must NEVER
    # appear in the core: x > 100 is hard; tracked x < 0 is the only tracker
    # needed. Minimal core = {neg}. Soundness/minimality here are relative to
    # the HARD asserts always being present (so we verify with them included).
    hard = [lambda: z.Int("x") > 100]
    tracked = {
        "neg": lambda: z.Int("x") < 0,
        "d1": lambda: z.Int("y") > 0,
    }
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        s.add(x > 100)  # hard, untracked
        s.assert_and_track(x < 0, z.Bool("neg"))
        s.assert_and_track(z.Int("y") > 0, z.Bool("d1"))
    assert s.check() == z.unsat
    core = s.unsat_core()
    names = [c.decl_name for c in core]
    name_set = set(names)
    # No fabricated / hard literals in the core.
    assert name_set.issubset(set(tracked))

    def recheck(subset):
        s2 = fresh_solver()
        with s2.using():
            for build in hard:
                s2.add(build())
            for nm in subset:
                s2.add(tracked[nm]())
        return s2.check()

    # SOUND: hard asserts + core trackers are UNSAT.
    assert recheck(names) == z.unsat
    # DELETION-MINIMAL: dropping any core tracker (hard asserts stay) is SAT.
    for drop in range(len(names)):
        remaining = names[:drop] + names[drop + 1:]
        assert recheck(remaining) == z.sat
    assert name_set == {"neg"}


# ---------------------------------------------------------------------------
# State sanity: minimization re-solves under subsets; the solver must be left
# in a consistent UNSAT state and unsat_core() must be idempotent.
# ---------------------------------------------------------------------------

def test_unsat_core_is_idempotent_and_leaves_unsat_state():
    builders = {
        "gt5": lambda: z.Int("x") > 5,
        "lt3": lambda: z.Int("x") < 3,
        "eq4": lambda: z.Int("x") == 4,
    }
    s = fresh_solver()
    with s.using():
        for nm, build in builders.items():
            s.assert_and_track(build(), z.Bool(nm))
    assert s.check() == z.unsat
    first = {c.decl_name for c in s.unsat_core()}
    # Calling again (after minimization re-solved internally) gives the same
    # minimal core, and the cached verdict is still UNSAT.
    second = {c.decl_name for c in s.unsat_core()}
    assert first == second
    assert len(first) == 2
    # A subsequent check() under the tracked set is still UNSAT (state intact).
    assert s.check() == z.unsat


def test_unsat_core_empty_when_sat_after_minimization_path():
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        s.assert_and_track(x > 5, z.Bool("p1"))
        s.assert_and_track(x < 100, z.Bool("p2"))
    assert s.check() == z.sat
    assert s.unsat_core() == []


def test_single_tracker_core_is_minimal():
    # A self-contradictory single tracked assert: minimal core is itself.
    builders = {"contra": lambda: z.And(z.Bool("a"), z.Not(z.Bool("a")))}
    s = fresh_solver()
    with s.using():
        s.assert_and_track(z.And(z.Bool("a"), z.Not(z.Bool("a"))), z.Bool("contra"))
    assert s.check() == z.unsat
    core = s.unsat_core()
    names = _assert_sound_and_minimal(core, builders, list(builders))
    assert names == {"contra"}


# ---------------------------------------------------------------------------
# Differential cross-check against the real z3py oracle (4.15.4).
# ---------------------------------------------------------------------------

@pytest.mark.skipif(not HAVE_Z3PY, reason="z3py not installed")
def test_crosscheck_unique_core_equals_z3py():
    # Unique minimal core → ayz3 and z3py MUST agree exactly on the set.
    # ayz3 side.
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        s.assert_and_track(x > 10, z.Bool("hi"))
        s.assert_and_track(x < 0, z.Bool("lo"))
        s.assert_and_track(z.Int("y") > 0, z.Bool("d1"))
        s.assert_and_track(z.Int("z") == 5, z.Bool("d2"))
    assert s.check() == z.unsat
    ay_names = {c.decl_name for c in s.unsat_core()}

    # z3py side (same instance).
    zs = _z3.Solver()
    zx = _z3.Int("x")
    zs.assert_and_track(zx > 10, _z3.Bool("hi"))
    zs.assert_and_track(zx < 0, _z3.Bool("lo"))
    zs.assert_and_track(_z3.Int("y") > 0, _z3.Bool("d1"))
    zs.assert_and_track(_z3.Int("z") == 5, _z3.Bool("d2"))
    assert str(zs.check()) == "unsat"
    z_names = {str(c) for c in zs.unsat_core()}

    # Unique minimal core → exact agreement.
    assert ay_names == z_names == {"hi", "lo"}


@pytest.mark.skipif(not HAVE_Z3PY, reason="z3py not installed")
def test_crosscheck_multiple_cores_same_minimal_size():
    # Multiple minimal cores → sizes must match z3py (both minimal), set may
    # differ. Verdicts must agree.
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        s.assert_and_track(x > 5, z.Bool("gt5"))
        s.assert_and_track(x < 3, z.Bool("lt3"))
        s.assert_and_track(x == 4, z.Bool("eq4"))
    ay_verdict = s.check()
    ay_names = {c.decl_name for c in s.unsat_core()}

    zs = _z3.Solver()
    zx = _z3.Int("x")
    zs.assert_and_track(zx > 5, _z3.Bool("gt5"))
    zs.assert_and_track(zx < 3, _z3.Bool("lt3"))
    zs.assert_and_track(zx == 4, _z3.Bool("eq4"))
    z_verdict = zs.check()
    z_names = {str(c) for c in zs.unsat_core()}

    assert str(ay_verdict) == str(z_verdict) == "unsat"
    # Both minimal → same size; both subsets of the full tracked set.
    assert len(ay_names) == len(z_names) == 2
    assert ay_names.issubset({"gt5", "lt3", "eq4"})
    assert z_names.issubset({"gt5", "lt3", "eq4"})


@pytest.mark.skipif(not HAVE_Z3PY, reason="z3py not installed")
def test_crosscheck_triple_core_equals_z3py():
    # x==1, y==1, x+y==3 : the unique minimal core is the whole triple.
    s = fresh_solver()
    with s.using():
        s.assert_and_track(z.Int("x") == 1, z.Bool("x1"))
        s.assert_and_track(z.Int("y") == 1, z.Bool("y1"))
        s.assert_and_track(z.Int("x") + z.Int("y") == 3, z.Bool("sum3"))
        s.assert_and_track(z.Int("k") > 0, z.Bool("d1"))
    assert s.check() == z.unsat
    ay_names = {c.decl_name for c in s.unsat_core()}

    zs = _z3.Solver()
    zs.assert_and_track(_z3.Int("x") == 1, _z3.Bool("x1"))
    zs.assert_and_track(_z3.Int("y") == 1, _z3.Bool("y1"))
    zs.assert_and_track(_z3.Int("x") + _z3.Int("y") == 3, _z3.Bool("sum3"))
    zs.assert_and_track(_z3.Int("k") > 0, _z3.Bool("d1"))
    assert str(zs.check()) == "unsat"
    z_names = {str(c) for c in zs.unsat_core()}

    assert ay_names == z_names == {"x1", "y1", "sum3"}


@pytest.mark.skipif(not HAVE_Z3PY, reason="z3py not installed")
def test_crosscheck_many_distractors_size_matches():
    # Larger over-determined instance: 1 conflict pair + many distractors.
    # ayz3's minimal core size must equal z3py's.
    s = fresh_solver()
    with s.using():
        s.assert_and_track(z.Int("x") > 1000, "C_hi")
        s.assert_and_track(z.Int("x") < -1000, "C_lo")
        for i in range(12):
            s.assert_and_track(z.Int(f"v{i}") >= i, f"d{i}")
    assert s.check() == z.unsat
    ay_names = {c.decl_name for c in s.unsat_core()}

    zs = _z3.Solver()
    zs.assert_and_track(_z3.Int("x") > 1000, "C_hi")
    zs.assert_and_track(_z3.Int("x") < -1000, "C_lo")
    for i in range(12):
        zs.assert_and_track(_z3.Int(f"v{i}") >= i, f"d{i}")
    assert str(zs.check()) == "unsat"
    z_names = {str(c) for c in zs.unsat_core()}

    assert ay_names == {"C_hi", "C_lo"}
    assert len(ay_names) == len(z_names)
