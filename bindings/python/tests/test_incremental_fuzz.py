# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# INCREMENTAL push/pop differential verdict fuzz test.
#
# Drives a random INCREMENTAL SESSION (interleaved push/pop/add/check, with
# occasional assert_and_track/unsat_core) over ONE long-lived solver, replays
# the IDENTICAL op sequence against BOTH ayz3 and real z3py, and compares the
# verdict at EVERY check point. A single sat-vs-unsat split at any check point is
# a high-priority verdict dispute requiring independent adjudication.
#
# CLASSIFICATION RULE: an `unknown` from ayz3 while z3 is decisive (or a
# binding gap that aborts the session) is INCOMPLETE -- recorded separately, NOT
# a bug. Only a genuine sat-vs-unsat split is a finding.
#
# SKIPS gracefully if real z3py is not installed (a differential test is
# meaningless without a reference solver).
#
# REGRESSION POLICY: historical array wrong-`unsat` seeds now fail closed with
# `unknown`. The incremental `arrays` / `arr_lia` fragments are held to the same
# zero-disagreement bar as every other tested fragment; incompleteness remains a
# separate, explicitly counted outcome.

import os

import pytest

from ayz3_fuzz import incremental

z3 = pytest.importorskip(
    "z3",
    reason="real z3py not installed; incremental differential fuzz needs a "
           "reference solver",
)

# Number of incremental sessions per fragment. Override with
# AYZ3_INCR_FUZZ_COUNT for a heavier local run.
DEFAULT_COUNT = int(os.environ.get("AYZ3_INCR_FUZZ_COUNT", "10"))
TIMEOUT_MS = int(os.environ.get("AYZ3_INCR_FUZZ_TIMEOUT_MS", "2000"))

# Fragments held to the strict zero-disagreement bar (AY's decided fragments,
# plus the combined/quantified ones the campaign found clean incrementally).
STRICT_FRAGMENTS = ["qf_lia", "qf_lra", "qf_bv", "qf_bv_bool", "qf_uflia",
                    "quant_lia"]


def _banner_for(summary, fragment):
    lines = []
    for seed in summary.disagreeing_seeds:
        res = incremental.run_session(fragment, seed, timeout_ms=TIMEOUT_MS)
        ops = incremental.generate_session(fragment, seed)
        lines.append(incremental.disagreement_banner(res, ops, z3))
    return "\n".join(lines)


@pytest.mark.parametrize("fragment", STRICT_FRAGMENTS)
def test_incremental_no_sat_unsat_disagreement(fragment):
    """No strict fragment may produce a single sat-vs-unsat disagreement at any
    incremental check point vs z3py."""
    summary = incremental.run_campaign(
        fragment, DEFAULT_COUNT, seed_start=0, timeout_ms=TIMEOUT_MS
    )
    assert summary.sessions == DEFAULT_COUNT
    # The campaign must actually have COMPARED some check points (not all
    # aborted/incomplete) -- otherwise a green here would be meaningless.
    assert summary.agree > 0, (
        f"fragment {fragment!r}: zero AGREE check points over "
        f"{summary.sessions} sessions (incomplete={summary.incomplete}); the "
        f"incremental cross-run did not meaningfully exercise z3"
    )
    assert summary.disagree == 0, (
        f"INCREMENTAL VERDICT DISPUTE: {summary.disagree} sat-vs-unsat "
        f"disagreement(s) in fragment {fragment!r} at seeds "
        f"{summary.disagreeing_seeds}.\n{_banner_for(summary, fragment)}"
    )


def test_incremental_qf_lia_clean():
    """Focused guard: ~10 incremental qf_lia sessions, zero soundness
    disagreement (the task's required smoke assertion)."""
    summary = incremental.run_campaign(
        "qf_lia", 10, seed_start=0, timeout_ms=TIMEOUT_MS
    )
    assert summary.disagree == 0, (
        f"qf_lia incremental sessions disagreed at seeds "
        f"{summary.disagreeing_seeds}"
    )
    assert summary.check_points > 0, "no check points were compared"


def test_incremental_session_is_deterministic():
    """A (fragment, seed) pair must regenerate the identical incremental session,
    so a disagreement reproduces exactly."""
    for fragment in incremental.FRAGMENTS:
        a = incremental.generate_session(fragment, 777)
        b = incremental.generate_session(fragment, 777)
        assert len(a) == len(b)
        assert [o.kind for o in a] == [o.kind for o in b], (
            f"non-deterministic session generation for {fragment!r}"
        )
        # Pop counts and tracker names must also match deterministically.
        assert [(o.kind, o.n, o.tracker) for o in a] == \
               [(o.kind, o.n, o.tracker) for o in b]


def test_incremental_sessions_are_well_bracketed():
    """Generated sessions must never pop more scopes than are open (a malformed
    session would itself crash, masking real bugs)."""
    for fragment in incremental.FRAGMENTS:
        for seed in range(25):
            depth = 0
            for op in incremental.generate_session(fragment, seed):
                if op.kind == "push":
                    depth += 1
                elif op.kind == "pop":
                    assert op.n <= depth, (
                        f"{fragment} seed {seed}: pop({op.n}) with depth {depth}"
                    )
                    depth -= op.n
            assert depth >= 0


def test_incremental_runs_push_pop_check_track():
    """A session must actually exercise the incremental ops (push/pop and at
    least one check); otherwise this fuzzer would be testing nothing
    incremental."""
    # Aggregate op kinds over a spread of seeds; the generator is weighted to
    # include all of them across a handful of sessions.
    kinds = set()
    for seed in range(20):
        for op in incremental.generate_session("qf_lia", seed):
            kinds.add(op.kind)
    assert {"push", "pop", "add", "check"} <= kinds, (
        f"incremental sessions did not exercise push/pop/add/check: {kinds}"
    )


@pytest.mark.parametrize("fragment", ["arrays", "arr_lia"])
def test_incremental_arrays_no_disagreement(fragment):
    """Incremental array sessions must never disagree with z3py.

    The session count is kept small with a tight per-check timeout because array
    sessions are slow. `unknown` remains an honest incompleteness result; a
    sat-vs-unsat split is a hard failure.
    """
    summary = incremental.run_campaign(
        fragment, 30, seed_start=0, timeout_ms=500
    )
    assert summary.disagree == 0, (
        f"{fragment}: {summary.disagree} incremental sat-vs-unsat "
        f"disagreement(s) at seeds {summary.disagreeing_seeds}"
    )
