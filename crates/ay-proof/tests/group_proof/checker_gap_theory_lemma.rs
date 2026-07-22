// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Documents a known proof checker gap: theory lemmas are accepted as
// axioms without semantic validation. See sat-debuggability epic #4172.

use super::common;

use ay_proof::check_proof;

/// The proof checker accepts semantically invalid theory lemmas.
///
/// Constructs a proof where:
/// - Assume x (true)
/// - Assume y (true)
/// - TheoryLemma from "FAKE_THEORY" claiming (not x, not y)
/// - Resolve (not x, not y) with (x) on pivot x → (not y)
/// - Resolve (not y) with (y) on pivot y → empty clause
///
/// No real theory can derive (not x, not y) from nothing. The proof
/// is structurally complete but semantically unsound. The checker
/// accepts it because `validate_step` pushes TheoryLemma clauses
/// directly into `derived_clauses` without verification (checker.rs:120).
///
/// This means proofs with bogus theory lemmas pass the checker.
/// For proof-based Craig interpolation (#4173), this is a soundness
/// risk: interpolants derived from invalid theory lemmas are incorrect.
///
/// Fixing requires either:
/// (a) theory-specific validation callbacks per TheoryLemmaKind, or
/// (b) strict mode that rejects TheoryLemma (like strict rejects Trust).
#[test]
fn test_checker_accepts_unvalidated_theory_lemma_gap() {
    let (terms, proof) = common::build_unsound_theory_lemma_proof();

    // GAP: semantically unsound proof passes the checker.
    check_proof(&proof, &terms)
        .expect("checker accepts bogus theory lemma (known gap: no semantic validation)");
}
