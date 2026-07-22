# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# B-5 SOLVER-SURFACE tests for ayz3: Solver.statistics() (+ the Statistics
# object), Solver.sexpr() / Solver.to_smt2(), and Solver.proof() (Alethe).
#
# HONESTY (the heart of these tests):
#   * Every statistic is a REAL AY solve counter read from the executor
#     snapshot; `num assertions` must equal the ACTUAL asserted count, and a
#     pre-check snapshot must be all-zero. Nothing is fabricated.
#   * The Statistics object matches z3py's core surface (len/keys/int-index
#     pair/get_key_value/attribute/repr); where z3py is installed we cross-check
#     the SHAPE (not the key set — AY's counter set differs from z3's, which is
#     a documented, honest divergence).
#   * sexpr() reparses to an EQUISATISFIABLE solver (verdict preserved); where
#     z3py is installed the verdict must AGREE with z3py's.
#   * proof() is fail-closed: it returns AY's real Alethe proof text ONLY after
#     an UNSAT check with production enabled, and raises honestly otherwise —
#     never a fabricated proof for sat/unknown or when production was off.
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


def _unsat_bool_solver():
    s = fresh_solver()
    with s.using():
        a, b = z.Bool("a"), z.Bool("b")
        s.add(z.Or(a, b), z.Not(a), z.Not(b))
    return s


# ===========================================================================
# 1. Statistics object shape
# ===========================================================================

def test_statistics_after_check_is_well_formed():
    s = _unsat_bool_solver()
    assert s.check() == z.unsat
    st = s.statistics()

    assert isinstance(len(st), int) and len(st) > 0
    keys = st.keys()
    assert isinstance(keys, list) and len(keys) == len(st)
    assert all(isinstance(k, str) and k for k in keys)

    # z3py: st[int] -> (key, value) pair.
    k0, v0 = st[0]
    assert isinstance(k0, str)
    assert isinstance(v0, (int, float))

    # Every entry is a real number via get_key_value.
    for k in keys:
        assert isinstance(st.get_key_value(k), (int, float))


def test_statistics_string_subscript_returns_number():
    # ergonomic superset the task asks for: st['conflicts'] -> int.
    s = _unsat_bool_solver()
    s.check()
    st = s.statistics()
    assert "conflicts" in st
    assert isinstance(st["conflicts"], int)


def test_statistics_num_assertions_is_real_count():
    # HONESTY: num assertions reflects the ACTUAL asserted count, not a guess.
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        s.add(x > 0, x < 10, x != 5)
    s.check()
    st = s.statistics()
    assert st["num assertions"] == 3


def test_statistics_repr_is_z3_shape():
    s = _unsat_bool_solver()
    s.check()
    r = repr(s.statistics())
    assert r.lstrip().startswith("(:")
    assert r.rstrip().endswith(")")
    assert ":conflicts" in r


def test_statistics_attribute_access():
    # z3py exposes stats as attributes with '_' for spaces.
    s = _unsat_bool_solver()
    s.check()
    st = s.statistics()
    assert isinstance(st.max_memory, (int, float))
    assert isinstance(st.num_assertions, int)


def test_statistics_before_check_is_zeroed():
    # HONESTY: no check has run, so all counters are zero (not fabricated).
    s = fresh_solver()
    st = s.statistics()
    assert st["conflicts"] == 0
    assert st["num assertions"] == 0


def test_statistics_get_missing_key():
    s = _unsat_bool_solver()
    s.check()
    st = s.statistics()
    assert st.get("definitely-not-a-key", "DEFAULT") == "DEFAULT"
    with pytest.raises(z.AyZ3Exception):
        st.get_key_value("definitely-not-a-key")


@pytest.mark.skipif(not HAVE_Z3PY, reason="z3py not installed")
def test_statistics_shape_crosscheck():
    # Same problem through ayz3 AND z3py: the STRUCTURAL shape must match. We do
    # NOT compare key sets — AY's counter set differs from z3's (documented).
    def probe(mod):
        s = mod.Solver()
        a, b = mod.Bool("a"), mod.Bool("b")
        s.add(mod.Or(a, b), mod.Not(a), mod.Not(b))
        r = s.check()
        st = s.statistics()
        keys = st.keys()
        k0, v0 = st[0]
        return {
            "result": str(r),
            "len_pos": isinstance(len(st), int) and len(st) > 0,
            "keys_str": isinstance(keys, list) and all(isinstance(k, str) for k in keys),
            "index_pair": isinstance(k0, str) and isinstance(v0, (int, float)),
            "values_numeric": all(isinstance(st.get_key_value(k), (int, float)) for k in keys),
            "repr_shape": repr(st).lstrip().startswith("(:"),
        }

    ay = probe(z)
    zp = probe(_z3)
    assert ay["result"] == zp["result"] == "unsat"
    for prop in ("len_pos", "keys_str", "index_pair", "values_numeric", "repr_shape"):
        assert ay[prop] == zp[prop] is True, f"{prop}: ayz3={ay[prop]} z3py={zp[prop]}"


# ===========================================================================
# 2. sexpr() / to_smt2()
# ===========================================================================

def test_sexpr_reparses_equisatisfiable():
    s = fresh_solver()
    with s.using():
        y = z.Int("y")
        s.add(y > 3, y < 10)
    text = s.sexpr()
    assert isinstance(text, str)
    assert "(assert" in text and "declare-fun" in text

    reparsed = fresh_solver()
    reparsed.from_string(text)
    assert reparsed.check() == s.check()


def test_to_smt2_has_check_sat_and_reparses():
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        s.add(x > 0, x < 3)
    smt2 = s.to_smt2()
    assert "(check-sat)" in smt2
    assert "(assert" in smt2

    reparsed = fresh_solver()
    reparsed.from_string(smt2)  # query commands are ignored on parse
    assert reparsed.check() == s.check() == z.sat


@pytest.mark.skipif(not HAVE_Z3PY, reason="z3py not installed")
def test_sexpr_verdict_agrees_with_z3py():
    # Build the same constraints, dump ayz3.sexpr(), and confirm both AY (on
    # reparse) and z3py agree on the verdict.
    s = fresh_solver()
    with s.using():
        x = z.Int("x")
        s.add(x * x == 2)  # UNSAT over the integers
    ay_reparse = fresh_solver()
    ay_reparse.from_string(s.sexpr())

    zs = _z3.Solver()
    zx = _z3.Int("x")
    zs.add(zx * zx == 2)

    assert str(ay_reparse.check()) == str(zs.check())


# ===========================================================================
# 3. proof()  (AY emits Alethe; documented divergence from z3 proof terms)
# ===========================================================================

def test_proof_returns_alethe_text_after_unsat():
    s = fresh_solver()
    s.set(proof=True)
    with s.using():
        p = z.Bool("p")
        s.add(p, z.Not(p))
    assert s.check() == z.unsat
    proof = s.proof()
    assert isinstance(proof, str) and proof
    # Real Alethe markers, never a placeholder / z3-proof-term fabrication.
    assert ("assume" in proof) or ("step" in proof) or ("(cl" in proof)


def test_proof_requires_production_enabled_and_does_not_poison():
    # Disabled: honest raise, and the context error must NOT poison a later
    # check() (which would spuriously raise).
    s = fresh_solver()
    with s.using():
        p = z.Bool("p")
        s.add(p, z.Not(p))
    assert s.check() == z.unsat
    with pytest.raises(z.AyZ3Exception):
        s.proof()
    # A subsequent check still works cleanly.
    assert s.check() == z.unsat


def test_proof_not_fabricated_for_sat():
    # Enabled but SAT: proof() must raise, never invent a proof.
    s = fresh_solver()
    s.set(proof=True)
    with s.using():
        x = z.Int("x")
        s.add(x > 0)
    assert s.check() == z.sat
    with pytest.raises(z.AyZ3Exception):
        s.proof()
