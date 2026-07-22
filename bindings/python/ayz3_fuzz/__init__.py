# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0
#
# ayz3_fuzz: a DIFFERENTIAL VERDICT/MODEL fuzzer for the AY solver, driven through
# its z3py-compatible Python binding (`ayz3`) and cross-checked against real
# z3py (`z3`).
#
# WHAT IT DOES
#   It generates random, well-typed SMT formulas over a toggleable set of
#   fragments (QF_LIA, QF_BV, QF_LRA, arrays), builds the SAME formula through
#   BOTH `ayz3` and `z3` with a single module-parameterized builder, runs
#   `Solver(); add(f); check()` on each, and flags any sat-vs-unsat
#   disagreement -- a high-priority dispute that requires adjudication.
#
# PAIRWISE CLASSIFICATION
#   * both sat  or both unsat                      -> AGREE (OK)
#   * either side unknown (or a binding gap raises
#     NotImplementedError for an unsupported op)   -> SKIP (sound
#                                                    incompleteness / binding
#                                                    gap, NOT a bug)
#   * one sat and the other unsat                  -> DISAGREE (fail loudly;
#                                                    neither side is presumed right)
#
#   On a `sat` verdict we additionally validate the model against the formula
#   for an extra soundness check where possible.
#
#   It NEVER flags `unknown`/incompleteness as a bug. A sat-vs-unsat split is a
#   finding to resolve with a trusted label, model validation, or proof checker.
#
# REPRODUCIBILITY
#   Everything is driven by a seeded PRNG. The fuzzer reports the exact seed
#   for every formula; a single (fragment, seed) pair regenerates the identical
#   formula, and the runner can emit its SMT-LIB (via z3py's `sexpr()`) for a
#   minimal repro.

from . import incremental
from .gen import FRAGMENTS, generate
from .differential import (
    DISAGREE,
    AGREE,
    SKIP,
    CAT_A,
    CAT_B,
    CAT_C,
    CaseResult,
    RunSummary,
    Disagreement,
    Finding,
    have_z3,
    run_case,
    run_campaign,
)

__all__ = [
    "incremental",
    "FRAGMENTS",
    "generate",
    "DISAGREE",
    "AGREE",
    "SKIP",
    "CAT_A",
    "CAT_B",
    "CAT_C",
    "CaseResult",
    "RunSummary",
    "Disagreement",
    "Finding",
    "have_z3",
    "run_case",
    "run_campaign",
]
