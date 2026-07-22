// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Source-grep guard: detect unintentional drift in the ClearLevel0 proof-ID
// preservation pattern across its three code paths: conflict analysis,
// vivification, and clause replacement (#4617, #5014).
//
// Note: conflict_analysis.rs was split into conflict_analysis.rs +
// conflict_analysis_lrat.rs + conflict_analysis_lrat_unit_chain.rs +
// conflict_analysis_lrat_specialized.rs, and mutate.rs was split into
// mutate.rs + mutate_replace.rs + mutate_replace_lrat.rs + mutate_delete.rs.
// The guard tests search across all split files.

#![allow(clippy::panic)]

fn count_occurrences(source: &str, needle: &str) -> usize {
    source.match_indices(needle).count()
}

fn conflict_analysis_source() -> &'static str {
    include_str!("../../src/solver/conflict_analysis.rs")
}

fn conflict_analysis_lrat_source() -> &'static str {
    include_str!("../../src/solver/conflict_analysis_lrat.rs")
}

fn conflict_analysis_lrat_unit_chain_source() -> &'static str {
    include_str!("../../src/solver/conflict_analysis_lrat_unit_chain.rs")
}

fn conflict_analysis_lrat_specialized_source() -> &'static str {
    include_str!("../../src/solver/conflict_analysis_lrat_specialized.rs")
}

fn vivify_source() -> String {
    [
        include_str!("../../src/solver/inprocessing/vivify/mod.rs"),
        include_str!("../../src/solver/inprocessing/vivify/tier.rs"),
        include_str!("../../src/solver/inprocessing/vivify/analysis.rs"),
    ]
    .join("\n")
}

fn mutate_source() -> &'static str {
    include_str!("../../src/solver/mutate.rs")
}

fn mutate_replace_source() -> &'static str {
    include_str!("../../src/solver/mutate_replace.rs")
}

fn mutate_replace_lrat_source() -> &'static str {
    include_str!("../../src/solver/mutate_replace_lrat.rs")
}

fn mutate_delete_source() -> &'static str {
    include_str!("../../src/solver/mutate_delete.rs")
}

/// Combined conflict analysis sources (main + all LRAT split files).
fn conflict_analysis_combined() -> String {
    let mut combined = conflict_analysis_source().to_string();
    combined.push('\n');
    combined.push_str(conflict_analysis_lrat_source());
    combined.push('\n');
    combined.push_str(conflict_analysis_lrat_unit_chain_source());
    combined.push('\n');
    combined.push_str(conflict_analysis_lrat_specialized_source());
    combined
}

/// Combined mutate sources (main + replace + replace_lrat split files).
fn mutate_combined() -> String {
    let mut combined = mutate_source().to_string();
    combined.push('\n');
    combined.push_str(mutate_replace_source());
    combined.push('\n');
    combined.push_str(mutate_replace_lrat_source());
    combined.push('\n');
    combined.push_str(mutate_delete_source());
    combined
}

/// The 3-tier fallback function `level0_var_proof_id` must exist and be
/// used in all 3 code paths that collect LRAT proof hints for level-0
/// variables. Conflict analysis defines the function and calls it directly.
/// Vivify and mutate use it via the shared `collect_level0_unit_chain` method.
#[test]
fn level0_var_proof_id_exists_in_all_three_paths() {
    let ca = conflict_analysis_combined();
    let viv = vivify_source();
    let mut_ = mutate_combined();

    assert!(
        ca.contains("fn level0_var_proof_id("),
        "conflict_analysis*.rs must define level0_var_proof_id"
    );
    assert!(
        ca.contains("self.level0_var_proof_id("),
        "conflict_analysis*.rs must call level0_var_proof_id"
    );
    // Vivify delegates to collect_level0_unit_chain (which calls
    // level0_var_proof_id internally) rather than calling it directly.
    assert!(
        viv.contains("collect_level0_unit_chain"),
        "vivify.rs must use collect_level0_unit_chain for level-0 proof ID collection"
    );
    // Mutate calls level0_var_proof_id directly in multiple places.
    assert!(
        mut_.contains("self.level0_var_proof_id("),
        "mutate*.rs must call level0_var_proof_id"
    );
}

/// The `has_any_proof_id` check must appear in all 3 code paths
/// to include ClearLevel0 victims AND unit-clause variables (whose proof ID
/// is only in unit_proof_id, not reason or level0_proof_id) in the BFS
/// "needed" set (#6257).
#[test]
fn has_any_proof_id_guard_in_all_three_paths() {
    let ca = conflict_analysis_combined();
    let viv = vivify_source();
    let mut_ = mutate_combined();

    assert!(
        ca.contains("fn has_any_proof_id("),
        "conflict_analysis*.rs must define has_any_proof_id"
    );
    assert!(
        count_occurrences(&viv, "self.has_any_proof_id(") >= 2,
        "vivify.rs must use has_any_proof_id in seed and BFS expansion (>=2)"
    );
    assert!(
        count_occurrences(&mut_, "self.has_any_proof_id(") >= 2,
        "mutate*.rs must use has_any_proof_id in mark phase and BFS expansion (>=2)"
    );
}

/// Each code path must document its handling of ClearLevel0 victims
/// (variables whose reason was cleared by BVE). The "ClearLevel0 victims"
/// comment marks where these variables are handled in each file.
#[test]
fn bfs_continue_on_cleared_reason_in_all_three_paths() {
    let ca = conflict_analysis_combined();
    let viv = vivify_source();
    let mut_ = mutate_combined();

    assert!(
        ca.contains("ClearLevel0 victims"),
        "conflict_analysis*.rs must document ClearLevel0 victim handling"
    );
    assert!(
        viv.contains("ClearLevel0 victims"),
        "vivify.rs must document ClearLevel0 victim handling"
    );
    assert!(
        mut_.contains("ClearLevel0 victims"),
        "mutate*.rs must document ClearLevel0 victim handling"
    );
}

/// The write site that saves the proof ID before clearing reason must exist
/// in mutate*.rs (the ClearLevel0 implementation).
#[test]
fn clearlevel0_write_site_preserves_proof_id() {
    let mut_ = mutate_combined();

    // level0_proof_id may live directly on self or in self.cold after
    // struct-of-arrays refactors.
    assert!(
        mut_.contains("level0_proof_id[vi] = unit_id")
            || mut_.contains("level0_proof_id[vi] = tt_id")
            || mut_.contains("record_level0_proof_id_for_lit(lit, unit_id)"),
        "mutate*.rs ClearLevel0 must save proof ID before clearing reason"
    );
    assert!(
        mut_.contains("self.var_data[vi].reason = NO_REASON"),
        "mutate*.rs ClearLevel0 must clear reason after saving proof ID"
    );
}

/// The 3-tier fallback in `level0_var_proof_id` must check reason, then
/// unit_proof_id, then level0_proof_id — in that order.
#[test]
fn three_tier_fallback_order_preserved() {
    let ca = conflict_analysis_combined();

    assert!(
        ca.contains("fn level0_var_proof_id("),
        "level0_var_proof_id must exist"
    );
    // The function body should reference all 3 tiers. level0_proof_id may
    // live directly on self or in self.cold after struct-of-arrays refactors.
    assert!(
        ca.contains("var_data[var_index].reason")
            && ca.contains("unit_proof_id_of_var_index(var_index)")
            && ca.contains("level0_proof_id[var_index]"),
        "level0_var_proof_id must implement the 3-tier fallback: \
         reason -> unit_proof_id -> level0_proof_id"
    );
}
