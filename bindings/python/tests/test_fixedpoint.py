# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Fixedpoint (CHC / Horn clauses) surface tests, cross-checked against real
# z3py 4.15.4 (every expected verdict below was produced by running the same
# program under `import z3` in a fresh process; see docstrings).
#
# Const-name hygiene: ayz3 interns consts by name across the pytest process, so
# every const/relation here uses the unique `chcfp_` prefix.

import pytest

from ayz3 import (
    And,
    BoolSort,
    Fixedpoint,
    Function,
    Int,
    IntSort,
    sat,
    unsat,
)


def _int_rel(name, arity=1):
    return Function(name, *([IntSort()] * arity), BoolSort())


# ---------------------------------------------------------------------------
# Headline: P(0), forall x. P(x) => P(x+1), query P(5) — reachable.
# z3py oracle: sat
# ---------------------------------------------------------------------------

def test_chcfp_headline_reachable_sat():
    fp = Fixedpoint()
    P = _int_rel("chcfp_P")
    x = Int("chcfp_x1")
    fp.register_relation(P)
    fp.declare_var(x)
    fp.rule(P(0))
    fp.rule(P(x + 1), P(x))
    assert fp.query(P(5)) == sat
    assert fp.get_answer() == "sat"


# ---------------------------------------------------------------------------
# Safe case: Q(0), forall x. Q(x) & x<100 => Q(x+1); Q with x>200 unreachable.
# z3py oracle: unsat (and Q(50) is sat).
# ---------------------------------------------------------------------------

def test_chcfp_bounded_counter_safe_unsat():
    fp = Fixedpoint()
    Q = _int_rel("chcfp_Q")
    x = Int("chcfp_x2")
    fp.register_relation(Q)
    fp.declare_var(x)
    fp.rule(Q(0))
    fp.rule(Q(x + 1), And(Q(x), x < 100))
    assert fp.query(And(Q(x), x > 200)) == unsat
    assert fp.get_answer() == "unsat"
    # Still-reachable ground point in the same system.
    assert fp.query(Q(50)) == sat


# ---------------------------------------------------------------------------
# Binary relation, list-shaped rule bodies, fact(), conjunctive goal.
# z3py oracle: sat (R doubles y each step: (0,1)..(10,1024), so y>500 hit).
# ---------------------------------------------------------------------------

def test_chcfp_binary_relation_fact_and_list_body():
    fp = Fixedpoint()
    R = _int_rel("chcfp_R", arity=2)
    x = Int("chcfp_x3")
    y = Int("chcfp_y3")
    fp.register_relation(R)
    fp.declare_var(x)
    fp.declare_var(y)
    fp.fact(R(0, 1))
    fp.rule(R(x + 1, y * 2), [R(x, y), x < 10])
    assert fp.query(And(R(x, y), y > 500)) == sat


# ---------------------------------------------------------------------------
# Already-quantified full rule (no declare_var), headline alternate spelling.
# z3py oracle: sat for S(7); unsat for a negative goal.
# ---------------------------------------------------------------------------

def test_chcfp_explicit_forall_rules():
    from ayz3 import ForAll, Implies

    fp = Fixedpoint()
    S = _int_rel("chcfp_S")
    x = Int("chcfp_x4")
    fp.register_relation(S)
    fp.rule(S(0))
    fp.rule(ForAll([x], Implies(S(x), S(x + 1))))
    assert fp.query(S(7)) == sat
    # S is {0,1,2,...}: nothing negative is derivable. z3py oracle: unsat.
    fp2 = Fixedpoint()
    T = _int_rel("chcfp_T")
    fp2.register_relation(T)
    fp2.declare_var(x)
    fp2.rule(T(0))
    fp2.rule(T(x + 1), T(x))
    assert fp2.query(And(T(x), x < 0)) == unsat


# ---------------------------------------------------------------------------
# query(*args) conjoins multiple goals (z3py oracle: same verdicts as And).
# ---------------------------------------------------------------------------

def test_chcfp_query_varargs_conjoined():
    fp = Fixedpoint()
    U = _int_rel("chcfp_U")
    x = Int("chcfp_x5")
    fp.register_relation(U)
    fp.declare_var(x)
    fp.rule(U(0))
    fp.rule(U(x + 1), And(U(x), x < 5))
    assert fp.query(U(x), x > 2) == sat
    assert fp.query(U(x), x > 50) == unsat


# ---------------------------------------------------------------------------
# Printing / introspection surface.
# ---------------------------------------------------------------------------

def test_chcfp_sexpr_and_repr():
    fp = Fixedpoint()
    V = _int_rel("chcfp_V")
    x = Int("chcfp_x6")
    fp.register_relation(V)
    fp.declare_var(x)
    fp.rule(V(0))
    fp.rule(V(x + 1), V(x))
    s = fp.sexpr()
    assert "(declare-rel chcfp_V (Int))" in s
    assert "(rule " in s
    assert repr(fp) == s
    assert fp.to_string() == s


# ---------------------------------------------------------------------------
# Honest NotImplementedError surface: the C fn is genuinely absent (nm-verified;
# only 8 Z3_fixedpoint_* symbols are exported by libay_ffi).
# ---------------------------------------------------------------------------

def test_chcfp_unbacked_methods_raise():
    fp = Fixedpoint()
    with pytest.raises(NotImplementedError, match="Z3_fixedpoint_set_params"):
        fp.set(engine="spacer")
    with pytest.raises(NotImplementedError, match="Z3_fixedpoint_assert"):
        fp.add(Int("chcfp_x7") > 0)
    with pytest.raises(NotImplementedError, match="Z3_fixedpoint_get_rules"):
        fp.get_rules()
    with pytest.raises(NotImplementedError, match="Z3_fixedpoint_from_string"):
        fp.parse_string("(declare-rel p ())")
    with pytest.raises(NotImplementedError,
                       match="Z3_fixedpoint_update_rule"):
        fp.update_rule(None, None, "r")


def test_chcfp_register_relation_validates():
    from ayz3 import AyZ3Exception

    fp = Fixedpoint()
    with pytest.raises(AyZ3Exception):
        fp.register_relation(Int("chcfp_x8"))  # not a FuncDeclRef
    bad = Function("chcfp_intrange", IntSort(), IntSort())
    with pytest.raises(AyZ3Exception):
        fp.register_relation(bad)  # non-Bool range
