// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #4751 ratchet for LIA preprocessing's substitution rounds.

/// EVERY in-place `VariableSubstitution` round in LIA preprocessing must mint
/// replayable propagation provenance.
///
/// The defect this pins: the `#8736 completeness` SECOND round rewrites the
/// mod/div-eliminated artifact list IN PLACE, and it shipped without the
/// `extend_propagated_value_provenance_from_var_subst` call its FIRST-round
/// twin already had. A rewritten assertion with no `before -> after` record is
/// never nominated by `propagation_replay_candidates`, so
/// `demote_non_problem_assumptions` stamps its `assume` a premiseless `trust`
/// and strict presentation rejects the proof.
///
/// Measured on the `dillig12_m` benchmark (`ay-chc`, #4751) with an env-gated
/// A/B over the SAME binary, 3 runs per arm, counting every premiseless
/// `Trust` step per rejected proof: 3/3/3 -> 0/0/0. Nothing was traded for it —
/// the `uses unverified trust rule` first-offender vanished, the
/// resource-envelope rejection count stayed at exactly 5, and no
/// `InvalidTheoryLemma` appeared, so no trust-kind rejection became a hard one.
///
/// The two rounds' gates deliberately DIFFER — a round runs under
/// `!is_producing_proofs()` while a mint runs under `produce_proofs_enabled()`
/// — so "this round is off under proofs" is NOT a reason to skip its mint: on
/// the CHC route the caller never requests a proof artifact
/// (`is_producing_proofs()` false in 1099 of 1099 probed calls) yet a tracker
/// IS recording for mandatory UNSAT certification (`produce_proofs_enabled()`
/// true in 1075 of them). That window is exactly where the rewrite happens and
/// where its provenance is needed.
///
/// Any NEW substitution round added to this pipeline must carry its own mint,
/// or this test fails.
#[test]
fn every_preprocess_var_subst_round_mints_provenance_4751() {
    let harness = include_str!("../mod.rs");
    let start = harness
        .find("fn preprocess_lia_artifacts")
        .expect("preprocess_lia_artifacts must exist");
    let rest = &harness[start..];
    let end = rest
        .find("fn preprocess_lia_assumptions")
        .expect("preprocess_lia_assumptions must follow preprocess_lia_artifacts");
    // The second round lives in its own module; scan both halves of the
    // pipeline so extracting a round cannot silently drop it from the ratchet.
    let sources = [&rest[..end], include_str!("../mod_elim_var_subst.rs")];

    let mut applies = 0usize;
    let mut mints = 0usize;
    for source in sources {
        // Comments name both symbols freely; only executable text counts.
        let code_only = source
            .lines()
            .map(|line| match line.find("//") {
                Some(idx) => &line[..idx],
                None => line,
            })
            .collect::<Vec<_>>()
            .join("\n");
        applies += code_only.matches("var_subst.apply").count();
        mints += code_only
            .matches("extend_propagated_value_provenance_from_var_subst")
            .count();
    }

    assert!(
        applies >= 2,
        "expected both LIA substitution rounds to be scanned, found {applies} apply sites"
    );
    assert_eq!(
        mints, applies,
        "every in-place VariableSubstitution round in LIA preprocessing must mint propagation \
         provenance (found {applies} apply sites but {mints} mints); a round without a mint \
         demotes its rewritten assertions to premiseless trust steps (#4751)"
    );
}
