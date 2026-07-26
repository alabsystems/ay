# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# Differential verdict/model fuzz test: generate random well-typed formulas, build
# each through BOTH ayz3 and real z3py, check both, and flag any sat-vs-unsat
# disagreement (a high-priority dispute requiring independent adjudication).
#
# This is the pytest entry point for the fuzzer in ayz3_fuzz/. It runs a bounded,
# DETERMINISTIC campaign per fragment (fixed seed sequence) so a failure
# reproduces exactly. The version-pinned real z3py oracle is a required dev
# dependency; conftest fails collection clearly when it is unavailable.
#
# CLASSIFICATION RULE: the comparison treats either side's `unknown` (or a binding
# gap) as a SKIP -- sound incompleteness is NOT a bug. Only a genuine
# sat-vs-unsat split is a finding. The test additionally surfaces (without
# failing the soundness assertion) any case where ayz3 reports `sat` but its own
# model fails to satisfy the formula -- a model-fidelity issue, not a wrong
# verdict.
#
# FORMERLY-KNOWN BUGS, NOW FIXED AND PINNED AS REGRESSIONS: this file used to
# document (as xfails + detector pins) two classes of open AY bugs:
#   * arrays wrong-`unsat` (CAT_A) at seeds 341/500/561 -- fixed by the array
#     soundness work on main; AY now answers `sat` (agreeing with z3) or an
#     HONEST `unknown`, never a wrong verdict, on those seeds.
#   * qf_bv wrong MODELS on Bool-conditioned `ite` (CAT_B) at seeds 5/432/439
#     -- fixed by the faithful BV model reconstruction on main; the models now
#     z3-validate.
# The pins below were updated to assert the CORRECT behavior (they fail loudly
# if either bug ever regresses), and the matching xfail markers were removed
# the moment they flipped to XPASS, as their own docstrings required.

import os

import pytest
import z3

from ayz3_fuzz import differential
from ayz3_fuzz.gen import FRAGMENTS

# Per-fragment formula count. Override with AYZ3_FUZZ_COUNT for a heavier local
# run (e.g. AYZ3_FUZZ_COUNT=2000 pytest -k diff_fuzz).
DEFAULT_COUNT = int(os.environ.get("AYZ3_FUZZ_COUNT", "300"))
TIMEOUT_MS = int(os.environ.get("AYZ3_FUZZ_TIMEOUT_MS", "2000"))

# Fragments held to the strict zero-DISAGREEMENT (CAT_A: sat-vs-unsat) bar --
# AY's strongest, decided fragments plus the new combined/quantified fragments
# that the inventory campaign found NO sat-vs-unsat disagreement in. `arrays`
# CAT_A is covered by its own 600-case campaign below (it historically carried
# a wrong-`unsat` bug, fixed on main and pinned as a regression here).
STRICT_FRAGMENTS = ["qf_bv", "qf_lia", "qf_lra", "qf_bv_bool", "qf_uflia",
                    "quant_lia"]

# Seeds where AY HISTORICALLY returned a WRONG `unsat` on a sat array formula
# (CAT_A) -- fixed on main; pinned so a regression fails loudly. On these seeds
# AY must never again produce a definitive verdict disagreeing with z3 (an
# honest `unknown`, e.g. under a tight timeout, remains acceptable).
FIXED_ARRAY_VIOLATION_SEEDS = (341, 500, 561)

# Seeds where AY HISTORICALLY returned `sat` with a MODEL that falsified the
# formula (CAT_B, Bool-conditioned BV `ite` model-construction) -- fixed on
# main; pinned to assert the models now z3-validate.
FIXED_BV_WRONG_MODEL_SEEDS = (5, 432, 439)


def _assert_no_disagreement(summary):
    """Fail loudly with a full repro banner if any disagreement was found."""
    if summary.disagree:
        banners = "\n".join(d.banner() for d in summary.disagreements)
        pytest.fail(
            f"VERDICT DISPUTE: {summary.disagree} sat-vs-unsat "
            f"disagreement(s) in fragment {summary.fragment!r}.\n{banners}",
            pytrace=False,
        )


@pytest.mark.parametrize("fragment", STRICT_FRAGMENTS)
def test_no_sat_unsat_disagreement(fragment):
    """No strict fragment may produce a single sat-vs-unsat disagreement vs z3py."""
    summary = differential.run_campaign(
        fragment, DEFAULT_COUNT, seed_start=0, timeout_ms=TIMEOUT_MS
    )
    # The campaign must actually have compared formulas against z3 (not all
    # skipped) -- otherwise a green here would be meaningless.
    assert summary.count == DEFAULT_COUNT
    assert summary.agree > 0, (
        f"fragment {fragment!r}: zero agreements over {summary.count} cases "
        f"(skip={summary.skip}); the cross-run did not meaningfully exercise z3"
    )
    _assert_no_disagreement(summary)


def test_arrays_no_sat_unsat_disagreement():
    """The arrays fragment must not disagree with z3py. This was an OPEN AY BUG
    (wrong 'unsat' on sat array formulas, seeds 341/500/561) documented here as
    an xfail until the array soundness fixes on main landed; the marker was
    removed when it flipped to XPASS, exactly as its docstring required. It is
    now a hard regression gate.
    """
    # 600 cases covers the historically-violating seeds (341/500/561).
    summary = differential.run_campaign(
        "arrays", 600, seed_start=0, timeout_ms=TIMEOUT_MS
    )
    _assert_no_disagreement(summary)


def test_fixed_array_violation_seeds_stay_fixed():
    """REGRESSION PIN (formerly `test_fuzzer_detects_known_array_violation`,
    which asserted the then-open bug: ayz3='unsat' vs z3='sat'). The array
    soundness fixes on main corrected AY's answers on these seeds, so the pin
    now asserts the CORRECT behavior: AY must never produce a definitive
    verdict that disagrees with z3 here. An honest `unknown` (sound
    incompleteness under the per-check timeout) is acceptable; a wrong `unsat`
    is the regression this test exists to catch.
    """
    from ayz3_fuzz.gen import generate, build

    for seed in FIXED_ARRAY_VIOLATION_SEEDS:
        case = differential.run_case("arrays", seed, timeout_ms=10000)
        # z3 still returns sat with a self-consistent model. Preserve that
        # evidence and fail on any renewed AY/z3 verdict dispute.
        node = generate("arrays", seed)
        fz = build(node, z3)
        sz = z3.Solver()
        sz.add(fz)
        assert str(sz.check()) == "sat"
        assert z3.is_true(sz.model().eval(fz, model_completion=True))
        assert case.outcome != differential.DISAGREE, (
            f"arrays seed {seed} REGRESSED: {case.outcome} "
            f"(ayz3={case.ay.verdict}, z3={case.z3.verdict})"
        )
        assert case.ay.verdict in ("sat", "unknown"), (
            f"arrays seed {seed}: AY answered {case.ay.verdict!r} on a "
            f"z3-proven-sat formula"
        )
        # When AY does answer sat, its own (full-model) evaluation of the
        # formula must not contradict its verdict.
        if case.ay.verdict == "sat":
            assert case.ay.own_eval is not False, (
                f"arrays seed {seed}: AY's own model falsifies the formula"
            )


def test_qf_bv_no_wrong_model():
    """qf_bv must produce no CAT_B wrong models. This was an OPEN AY BUG
    (models falsifying the formula on Bool-conditioned BV `ite`, seeds
    5/432/439) documented here as an xfail until the faithful BV model
    reconstruction on main landed; the marker was removed when it flipped to
    XPASS, exactly as its docstring required. Now a hard regression gate.
    """
    summary = differential.run_campaign(
        "qf_bv", 500, seed_start=0, timeout_ms=TIMEOUT_MS, max_findings_per_cat=3
    )
    assert summary.model_invalid == 0, (
        f"qf_bv: {summary.model_invalid} CAT_B wrong-model(s) "
        f"(AY sat but model falsifies the formula)"
    )


def test_fixed_bv_wrong_model_seeds_stay_fixed():
    """REGRESSION PIN (formerly `test_fuzzer_detects_known_bv_wrong_model`,
    which asserted the then-open bug with three confirmations of wrongness).
    The BV model reconstruction fixes on main corrected these witnesses, so
    the pin now asserts the CORRECT behavior with the same three independent
    checks, inverted: (1) the extracted scalar model, pinned in z3, keeps the
    formula sat; (2) the same holds via rendered-SMT-LIB reparse; and (3) AY's
    own model.eval(formula) returns True.
    """
    from ayz3_fuzz.gen import generate, build

    for seed in FIXED_BV_WRONG_MODEL_SEEDS:
        case = differential.run_case("qf_bv", seed, timeout_ms=10000)
        assert case.outcome == differential.AGREE
        assert case.ay.verdict == "sat" and case.z3.verdict == "sat"
        # (1) extracted scalar model is complete and z3-validates.
        assert case.ay.model_complete and case.ay.assignment
        assert case.ay.model_ok is True, (
            f"qf_bv seed {seed} REGRESSED: AY's model failed z3 validation"
        )
        node = generate("qf_bv", seed)
        # (2) rendered-SMT-LIB reparse of the pinned model is also sat.
        assert differential._reconfirm_wrong_model_via_smtlib(
            node, case.ay.assignment, z3) is True
        # (3) AY's own evaluator confirms its model satisfies the formula.
        assert differential._own_eval_satisfies(node, differential._load_ayz3()) is True
        # And the formula itself is genuinely sat (verdict cross-checked).
        fz = build(node, z3); sz = z3.Solver(); sz.add(fz)
        assert str(sz.check()) == "sat"


def test_uf_partial_model_is_not_a_bug():
    """HONESTY GUARD (CAT_C): the qf_uflia case at seed 89 -- f(3*i0) > f(i0)
    with model i0=0 -- must NOT be reported as a wrong model. Pinning only the
    scalar i0=0 forces f(0) > f(0) (trivially unsat) because the model OMITS the
    uninterpreted function's interpretation; AY's own model.eval returns True, so
    this is a PARTIAL model (not a bug). The categorizer must classify it CAT_C.
    """
    summary = differential.run_campaign(
        "qf_uflia", 300, seed_start=0, timeout_ms=TIMEOUT_MS
    )
    # No CAT_A and no genuine CAT_B; the seed-89 partial model is counted as a
    # partial (CAT_C) occurrence, never a wrong-model finding.
    assert summary.disagree == 0, "qf_uflia must have no sat-vs-unsat disagreement"
    assert summary.model_invalid == 0, (
        "qf_uflia: a partial UF model was misreported as a wrong model (CAT_B); "
        "it must be classified CAT_C (not a bug)"
    )
    assert summary.model_partial >= 1, (
        "qf_uflia seed 89 should be counted as a partial-model (CAT_C) occurrence"
    )


def test_arr_lia_no_wrong_model():
    """arrays+LIA must produce no CAT_B wrong models. The CAT_B reports this
    xfail used to document were manufactured by the C-API model surface itself
    (live-solver-state `Z3_model_eval` + the numeral-string handle-number fake
    feeding garbage into the scalar pin), not by the engine: with the snapshot
    model surface fixed in ay-ffi, the identical engine produces 0 CAT_B here
    (arr_lia 500-seed campaign: 15 -> 0). The marker was removed when it
    flipped to XPASS, as its docstring required. Now a hard regression gate.
    """
    # 120 cases already cover several arr_lia CAT_B wrong-models; a tighter
    # per-check timeout keeps this bounded (slow array cases SKIP, not hang).
    summary = differential.run_campaign(
        "arr_lia", 120, seed_start=0, timeout_ms=min(TIMEOUT_MS, 1000),
        max_findings_per_cat=3,
    )
    assert summary.model_invalid == 0, (
        f"arr_lia: {summary.model_invalid} CAT_B wrong-model(s)"
    )


def test_reference_solver_present():
    """The differential test is only meaningful with real z3py installed."""
    assert differential.have_z3(), "z3py reference solver must be importable"


def test_generation_is_deterministic():
    """A (fragment, seed) pair must regenerate the identical formula, so a
    failing case reproduces exactly."""
    from ayz3_fuzz.gen import generate

    for fragment in sorted(FRAGMENTS):
        a = generate(fragment, 12345)
        b = generate(fragment, 12345)
        # Rendering through z3 gives a canonical, comparable string.
        sa = differential._smtlib_for(a, z3)
        sb = differential._smtlib_for(b, z3)
        assert sa == sb, f"non-deterministic generation for {fragment!r}"
