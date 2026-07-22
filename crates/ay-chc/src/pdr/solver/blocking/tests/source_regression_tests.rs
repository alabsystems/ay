// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

const BLOCKING_SOURCES: &[(&str, &str)] = &[
    ("mod.rs", include_str!("../mod.rs")),
    ("lemma.rs", include_str!("../lemma.rs")),
    (
        "reachability/mod.rs",
        include_str!("../reachability/mod.rs"),
    ),
    (
        "reachability/single_body.rs",
        include_str!("../reachability/single_body.rs"),
    ),
    ("generalization.rs", include_str!("../generalization.rs")),
    (
        "bv_generalization.rs",
        include_str!("../bv_generalization.rs"),
    ),
    (
        "bool_normalization.rs",
        include_str!("../bool_normalization.rs"),
    ),
    (
        "global_generalize.rs",
        include_str!("../global_generalize.rs"),
    ),
    ("utils.rs", include_str!("../utils.rs")),
    ("interpolation.rs", include_str!("../interpolation.rs")),
    (
        "lemma_refinement.rs",
        include_str!("../lemma_refinement.rs"),
    ),
];

fn blocking_source_containing(needle: &str) -> (&'static str, &'static str) {
    BLOCKING_SOURCES
        .iter()
        .find(|(_, source)| source.contains(needle))
        .copied()
        .unwrap_or_else(|| panic!("expected blocking source containing `{needle}`"))
}

#[test]
fn sign_strengthening_non_self_inductive_branch_is_not_verbose_gated() {
    // Structural regression for #5877. P1:1561 found that the "inductive but
    // not self-inductive" branch accidentally used `else if self.config.verbose`,
    // which dropped `strengthened = candidate` whenever verbose logging was off.
    // Existing BV end-to-end regressions do not distinguish the broken and fixed
    // paths, so pin the control-flow shape until a smaller semantic reproducer
    // is available.
    let needle = "\"PDR: #5877 Sign constraint {} is inductive but not self-inductive, keeping\",";
    let (file, source) = blocking_source_containing(needle);
    let start = source
        .find(needle)
        .expect("expected #5877 non-self-inductive sign-strengthening log");
    let window_start = start.saturating_sub(200);
    let window_end = (start + 500).min(source.len());
    let window = &source[window_start..window_end];

    assert!(
        !window.contains("} else if self.config.verbose {"),
        "non-self-inductive sign strengthening in {file} must not gate candidate retention on verbose"
    );
    assert!(
        window
            .contains("} else {\n                                        if self.config.verbose {"),
        "expected verbose logging to be nested inside the non-self-inductive branch in {file}"
    );
    assert!(
        window.contains("// Still add it") && window.contains("strengthened = candidate;"),
        "expected the non-self-inductive branch in {file} to retain the strengthened candidate"
    );
}

#[test]
fn n1_per_clause_path_preserves_interpolant_kind_for_packet_2() {
    // Structural regression for #5877. The direct-PDR nested4 path reaches
    // blocking via try_n1_per_clause_interpolation(). If that helper returns
    // only `ChcExpr`, Packet 2 cannot detect DirectIucCoreExact candidates and
    // raw BV clauses are weakened before first admission.
    let expr_utils = include_str!("../../expr/interpolation.rs");
    assert!(
        expr_utils.contains(") -> Option<InterpolantCandidate> {"),
        "N1 per-clause interpolation must return InterpolantCandidate so provenance reaches blocking"
    );
    assert!(
        expr_utils.contains("compute_interpolant_candidate_from_smt_farkas_history("),
        "N1 per-clause interpolation must preserve interpolant kind metadata"
    );

    let needle = "if let Some(candidate) = self.try_n1_per_clause_interpolation(";
    let (file, blocking) = blocking_source_containing(needle);
    let start = blocking
        .find(needle)
        .expect("expected N1 per-clause interpolation branch in blocking.rs");
    let window_end = (start + 900).min(blocking.len());
    let window = &blocking[start..window_end];
    assert!(
        window.contains("let kind = candidate.kind;")
            && window.contains("interpolant_kind = Some(kind);"),
        "{file} must capture N1 interpolant kind before the BV weakening gate"
    );
}

#[test]
fn packet_2_skip_gate_preserves_direct_iuc_validated_bv_clauses() {
    // Structural regression for #5877. Zero-Farkas BV interpolation often
    // returns a Craig-validated direct-IUC core that is not `core_exact`.
    // Packet 2 still needs to preserve that raw clause on first admission.
    let (file, blocking) = blocking_source_containing(
        "InterpolantKind::DirectIucCoreExact | InterpolantKind::DirectIucValidated",
    );
    assert!(
        blocking
            .contains("InterpolantKind::DirectIucCoreExact | InterpolantKind::DirectIucValidated"),
        "Packet 2 must skip BV weakening for both direct-IUC variants in {file}"
    );
}

#[test]
fn direct_iuc_skip_gate_runs_bv_flag_guard_generalizer() {
    // Structural regression for #5877. The direct-IUC skip path now allows one
    // narrow weakening step for `x = 1` BV flag guards before skipping the
    // broader BV weakening stack.
    let needle = "let generalized = if skip_bv_weakening {";
    let (file, blocking) = blocking_source_containing(needle);
    let start = blocking
        .find(needle)
        .expect("expected direct-IUC skip gate in blocking.rs");
    let window_end = (start + 900).min(blocking.len());
    let window = &blocking[start..window_end];

    assert!(
        window.contains("BvFlagGuardGeneralizer::new().generalize("),
        "direct-IUC skip branch in {file} must run BvFlagGuardGeneralizer before returning"
    );
    assert!(
        window.contains("BV flag-guard weakening on direct-IUC"),
        "expected direct-IUC flag-guard diagnostic in the skip branch in {file}"
    );
}

#[test]
fn bv_blocking_path_tries_raw_iuc_before_inductive_fallback() {
    // Structural regression for #5877. The BV branch must not bypass the raw
    // IUC candidate path entirely; otherwise Packet 2's direct-IUC preservation
    // can never influence nested4-style BV convergence.
    let needle = "if pred_has_bv && !self.problem_is_pure_lia {";
    let (file, blocking) = blocking_source_containing(needle);
    let start = blocking
        .find(needle)
        .expect("expected BV blocking branch in blocking.rs");
    let window_end = (start + 1800).min(blocking.len());
    let window = &blocking[start..window_end];

    let iuc_start = window
        .find("if let Some(candidate) = self.try_iuc_farkas_fallback_candidate(")
        .expect("BV branch must try raw IUC candidate");
    let fallback_start = window
        .find("self.generalize_bv_inductive(&pob.state, pob.predicate, pob.level)")
        .expect("BV branch must retain inductive fallback");

    assert!(
        iuc_start < fallback_start,
        "BV blocking branch in {file} must try raw IUC before falling back to generalize_bv_inductive"
    );
}

#[test]
fn bv_predecessor_cube_selection_delegates_to_centralized_mbp_gate() {
    // Structural regression for #5877 Packet 2. The SAT predecessor paths
    // in the blocking module must delegate cube policy to core.rs via cube_with_mbp()
    // rather than carrying duplicated BV skip heuristics locally.
    // After the blocking.rs -> blocking/ module split, calls span blocking.rs,
    // blocking/reachability/mod.rs, and blocking/reachability/single_body.rs.
    let blocking_main = include_str!("../mod.rs");
    let blocking_reach_mod = include_str!("../reachability/mod.rs");
    let blocking_reach_single = include_str!("../reachability/single_body.rs");
    assert!(
        !blocking_main.contains("let cube = if bv_pred && !self.problem_is_pure_lia {"),
        "blocking.rs should not duplicate BV MBP eligibility branches at each predecessor site"
    );
    let total_calls = blocking_main.matches("self.cube_with_mbp(").count()
        + blocking_reach_mod.matches("self.cube_with_mbp(").count()
        + blocking_reach_single.matches("self.cube_with_mbp(").count();
    assert!(
        total_calls >= 5,
        "blocking module should route predecessor cube selection through cube_with_mbp (found {total_calls}, expected >=5)"
    );
}

#[test]
fn predecessor_reachability_rotates_clause_indices_without_bulk_clause_cloning_9719() {
    let reachability = include_str!("../reachability/mod.rs");
    let collect_start = reachability
        .find("let eligible_clause_indices: Vec<usize>")
        .expect("predecessor reachability should collect rotatable clause indices");
    let loop_start = reachability[collect_start..]
        .find("for offset in 0..eligible_clause_indices.len()")
        .map(|offset| collect_start + offset)
        .expect("predecessor reachability should rotate over collected indices");
    let collection_block = &reachability[collect_start..loop_start];

    assert!(
        collection_block.contains(".clauses_defining_with_index(pob.predicate)")
            && collection_block.contains(".map(|(index, _)| index)")
            && collection_block.contains(".collect()"),
        "#9719: predecessor reachability should collect only clause indices for rotation"
    );
    assert!(
        !collection_block.contains(".cloned()"),
        "#9719: predecessor reachability must not clone every defining clause before rotation"
    );

    let loop_window_end = (loop_start + 300).min(reachability.len());
    let loop_window = &reachability[loop_start..loop_window_end];
    assert!(
        loop_window.contains(
            "eligible_clause_indices[(rotation + offset) % eligible_clause_indices.len()]"
        ) && loop_window.contains("self.problem.clauses()[clause_index].clone()"),
        "#9719: reachability should clone only the currently checked rotated clause"
    );
}

#[test]
fn level_zero_fact_reachability_uses_indexed_defining_clause_scan_9719() {
    let blocking = include_str!("../mod.rs");
    let level0_start = blocking
        .find("if pob.level == 0 {")
        .expect("blocking should have a level-0 fact reachability path");
    let level0_slice = &blocking[level0_start..];
    let level0_end = level0_slice
        .find("// Step 2: Check reachability.")
        .unwrap_or(level0_slice.len());
    let level0_block = &level0_slice[..level0_end];

    assert!(
        level0_block.contains(".clauses_defining_with_index(pob.predicate)")
            && level0_block.contains(".filter(|(_, clause)| clause.is_fact())"),
        "#9719: level-0 fact scans should keep clause indices while skipping unrelated clauses"
    );
    assert!(
        !level0_block.contains(".clauses_defining(pob.predicate)")
            && !level0_block.contains(".filter(|clause| clause.is_fact())"),
        "#9719: level-0 fact scans must not use an unindexed defining-clause iterator"
    );
}
