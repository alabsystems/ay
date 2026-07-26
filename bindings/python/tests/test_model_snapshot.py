# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Regression tests for the C-API MODEL SNAPSHOT surface (model_params.rs):
#
#   FAKE #1 (removed): Z3_model_eval ignored `model_completion` and fell back
#           to LIVE solver state for compound terms (stale-model reads), with
#           hard `return 0` for Array/Seq/Uninterpreted values. It now
#           evaluates against the model snapshot only: substitute every
#           model-pinned constant with its snapshot value, re-fold, and return
#           either a literal or an HONEST partial evaluation — never a
#           fabricated value, never live solver state.
#
#   FAKE #2 (removed): Z3_model_get_num_consts counted entries (arrays
#           included) that Z3_model_get_const_decl did not enumerate, so every
#           model containing an array showed unnamed `= None` decls
#           (ayz3_fuzz arrays seed 96). num_consts/get_const_decl now share
#           one index space covering ALL sorts.
#
#   FAKE #3 (removed): Z3_get_numeral_string returned the AST HANDLE NUMBER as
#           a fake numeral string for non-numeral ASTs, so an unreduced eval
#           result read back as a garbage integer. It now returns NULL and the
#           binding raises honestly.
#
# Where a value is claimed, it is cross-checked against real z3py 4.15.4.
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


def _array_case(m):
    """Build (select a 3) = 7 AND i = 4 AND (select a i) = 1 in module `m`.

    Returns (solver, scope, a, i). The formula pins a[3] = 7 and a[4] = 1.
    """
    if m is z:
        s = fresh_solver()
        scope = s.using()
    else:
        s = m.Solver()

        class _N:
            def __enter__(self):
                return None

            def __exit__(self, *exc):
                return False

        scope = _N()
    with scope:
        a = m.Array('a', m.IntSort(), m.IntSort())
        i = m.Int('i')
        s.add(a[3] == 7, i == 4, a[i] == 1)
    return s, scope, a, i


# ===========================================================================
# FAKE #2 — decl enumeration alignment (arrays included, every entry named)
# ===========================================================================

def test_model_decls_all_named_with_interps_arrays_included():
    s, scope, a, i = _array_case(z)
    with scope:
        assert str(s.check()) == 'sat'
        m = s.model()
        decls = m.decls()
        names = [d.name() for d in decls]
        assert all(names), f"every model decl must be named, got {names}"
        assert 'a' in names, f"array const must be enumerated: {names}"
        assert 'i' in names, f"int const must be enumerated: {names}"
        for d in decls:
            assert m[d] is not None, f"decl {d.name()} must have an interp"
        # The repr regression from arrays seed 96: no '= None' placeholders.
        assert '= None' not in repr(m), repr(m)


# ===========================================================================
# FAKE #1 — snapshot evaluation (values, completion, staleness)
# ===========================================================================

def test_eval_array_selects_match_z3_semantics():
    s, scope, a, i = _array_case(z)
    with scope:
        assert str(s.check()) == 'sat'
        m = s.model()
        assert m.eval(a[3], model_completion=False).as_long() == 7
        assert m.eval(a[i], model_completion=False).as_long() == 1


@pytest.mark.usefixtures("required_reference_z3")
def test_eval_array_values_z3_pinned():
    """z3-pin the snapshot's claims: a[3]=7 and a[4]=1 must be consistent
    with the asserted formula in REAL z3 (never trust our own reduction)."""
    s, scope, a, i = _array_case(z)
    with scope:
        assert str(s.check()) == 'sat'
        m = s.model()
        v3 = m.eval(a[3], model_completion=False).as_long()
        v4 = m.eval(a[4], model_completion=False).as_long()
        iv = m.eval(i, model_completion=False).as_long()
    zs = _z3.Solver()
    za = _z3.Array('a', _z3.IntSort(), _z3.IntSort())
    zi = _z3.Int('i')
    zs.add(za[3] == 7, zi == 4, za[zi] == 1)
    zs.add(za[3] == v3, za[4] == v4, zi == iv)
    assert str(zs.check()) == 'sat', (
        f"snapshot readouts a[3]={v3}, a[4]={v4}, i={iv} must satisfy the formula"
    )


def test_eval_reads_snapshot_not_live_solver_state():
    """The stale-model bug: after the solver moves on (push + UNSAT), the old
    model handle must keep answering from its snapshot."""
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        s.add(x == 5)
        assert str(s.check()) == 'sat'
        m = s.model()
        s.push()
        s.add(x == 10)
        assert str(s.check()) == 'unsat'
        # Leaf and compound reads still come from the snapshot.
        assert m.eval(x, model_completion=False).as_long() == 5
        assert m.eval(x + x, model_completion=False).as_long() == 10
        s.pop()


def test_model_completion_identity_vs_default():
    """Z3 semantics (verified against z3py 4.15.4): an unpinned constant is
    the identity under model_completion=False and the per-sort default under
    True."""
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        s.add(x == 5)
        assert str(s.check()) == 'sat'
        m = s.model()
        # Declared AFTER the check: genuinely absent from the snapshot.
        fresh = z.Int('fresh_const_after_check')
        ident = m.eval(fresh, model_completion=False)
        with pytest.raises(z.AyZ3Exception):
            ident.as_long()  # identity result is NOT a numeral (fake #3 gone)
        assert m.eval(fresh, model_completion=True).as_long() == 0
        assert m.eval(z.Bool('fresh_bool'), model_completion=True).as_bool() is False
        # Compound: partial under False (honest), completed under True.
        partial = m.eval(x + fresh, model_completion=False)
        with pytest.raises(z.AyZ3Exception):
            partial.as_long()
        assert m.eval(x + fresh, model_completion=True).as_long() == 5


def test_whole_formula_own_eval_true_arrays_seed96_class():
    """The arrays-fragment arbiter pattern: model.eval(formula) on the model's
    OWN formula must reduce to True for a valid witness (pre-fix this read
    live solver state and produced spurious False -> fake CAT_B floods)."""
    s, scope, a, i = _array_case(z)
    with scope:
        f = z.And(a[3] == 7, i == 4, a[i] == 1)
        assert str(s.check()) == 'sat'
        m = s.model()
        assert m.eval(f, model_completion=True).as_bool() is True


# ===========================================================================
# FAKE #3 — Z3_get_numeral_string honesty
# ===========================================================================

def test_non_numeral_reads_raise_instead_of_handle_number():
    s = fresh_solver()
    with s.using():
        x = z.Int('x')
        s.add(x > 0)
        assert str(s.check()) == 'sat'
        # A variable AST is not a numeral: as_long() must raise, never return
        # the AST handle number as a fake value.
        with pytest.raises(z.AyZ3Exception):
            x.as_long()
