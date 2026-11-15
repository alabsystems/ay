// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_to_json_contains_required_fields() {
    let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::from_millis(42));
    stats.insert("conflicts", 1234);
    stats.insert("decisions", 5678);
    stats.insert_text("sat.capability.preprocess.state", "on");

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    assert_eq!(parsed["mode"], "dimacs-sat");
    assert_eq!(parsed["result"], "sat");
    assert_eq!(parsed["wall_time_ms"], 42);
    assert_eq!(parsed["ay_build"]["stamp"], BUILD_PROVENANCE.stamp);
    assert_eq!(parsed["conflicts"], 1234);
    assert_eq!(parsed["decisions"], 5678);
    assert_eq!(parsed["sat.capability.preprocess.state"], "on");
    assert!(
        parsed.get("competition_jit").is_none(),
        "competition JIT metadata should only appear when attached"
    );
}

#[test]
fn test_to_json_suppresses_retired_sat_propagation_counters() {
    let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::ZERO);
    stats.insert("sat.native_code_helpers_enabled", 1);
    stats.insert("sat.retired_propagation_compiler_rounds", 2);
    stats.insert("sat.propagation_native_active", 1);
    stats.insert("sat.propagation_native_propagations", 3);

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    assert_eq!(parsed["sat.native_code_helpers_enabled"], 1);
    assert!(
        parsed
            .as_object()
            .expect("stats JSON should be an object")
            .keys()
            .all(|key| !is_retired_sat_propagation_counter(key)),
        "retired SAT propagation counters must not appear in stats JSON: {parsed}"
    );
}

#[test]
fn test_to_json_contains_competition_jit_evidence_with_counter() {
    let mut stats = RunStatistics::new(SolveMode::Pb, "sat", Duration::from_millis(7));
    stats.insert("pb_pbo_candidate_applications", 9);
    stats.competition_jit = Some(CompetitionJitEvidence {
        track: "pb".to_string(),
        artifact_id: "pb-pbo-candidates".to_string(),
        candidate_mode: "solver-program".to_string(),
        application_counter: Some(CompetitionJitApplicationCounter {
            key: "pb_pbo_candidate_applications".to_string(),
            value: 9,
        }),
    });

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    let evidence = &parsed["competition_jit"];
    assert_eq!(evidence["schema_version"], 1);
    assert_eq!(evidence["track"], "pb");
    assert_eq!(evidence["artifact_id"], "pb-pbo-candidates");
    assert_eq!(evidence["artifact"], "pb-pbo-candidates");
    assert_eq!(evidence["candidate_mode"], "solver-program");
    assert_eq!(evidence["requested_mode"], "solver-program");
    assert_eq!(evidence["native_dispatch"], false);
    assert_eq!(evidence["fail_closed"], false);
    assert_eq!(
        evidence["application_counter"]["key"],
        "pb_pbo_candidate_applications"
    );
    assert_eq!(evidence["application_counter"]["value"], 9);
    assert_eq!(parsed["pb_pbo_candidate_applications"], 9);
}

#[test]
fn test_to_json_contains_competition_jit_evidence_without_counter() {
    let mut stats = RunStatistics::new(SolveMode::DimacsSat, "unknown", Duration::ZERO);
    stats.competition_jit = Some(CompetitionJitEvidence {
        track: "sat".to_string(),
        artifact_id: "sat-native-code-helpers".to_string(),
        candidate_mode: "current".to_string(),
        application_counter: None,
    });

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    let evidence = &parsed["competition_jit"];
    assert_eq!(evidence["schema_version"], 1);
    assert_eq!(evidence["track"], "sat");
    assert_eq!(evidence["artifact_id"], "sat-native-code-helpers");
    assert_eq!(evidence["artifact"], "sat-native-code-helpers");
    assert_eq!(evidence["candidate_mode"], "current");
    assert_eq!(evidence["requested_mode"], "current");
    assert_eq!(evidence["native_dispatch"], false);
    assert_eq!(evidence["fail_closed"], true);
    assert!(
        evidence.get("application_counter").is_none(),
        "application counter should be omitted when not applicable"
    );
}

#[test]
fn test_to_json_competition_jit_current_mode_with_applications_dispatches_native() {
    let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::ZERO);
    stats.competition_jit = Some(CompetitionJitEvidence {
        track: "sat".to_string(),
        artifact_id: "sat-native-code-helpers".to_string(),
        candidate_mode: "current".to_string(),
        application_counter: Some(CompetitionJitApplicationCounter {
            key: "sat.native_code_helper_applications".to_string(),
            value: 3,
        }),
    });

    let json_str = stats.to_json();
    let parsed: serde_json::Value =
        serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

    let evidence = &parsed["competition_jit"];
    assert_eq!(evidence["requested_mode"], "current");
    assert_eq!(evidence["candidate_mode"], "current");
    assert_eq!(evidence["native_dispatch"], true);
    assert_eq!(evidence["fail_closed"], false);
}

#[test]
fn test_build_provenance_helpers_include_build_stamp() {
    assert_eq!(
        BUILD_PROVENANCE.json_value()["stamp"],
        serde_json::Value::String(BUILD_PROVENANCE.stamp.to_string())
    );
    assert!(
        BUILD_PROVENANCE
            .human_banner()
            .contains(BUILD_PROVENANCE.stamp),
        "human banner should expose the active build stamp"
    );
    assert!(
        BUILD_PROVENANCE
            .comment_line()
            .contains(BUILD_PROVENANCE.stamp),
        "comment line should expose the active build stamp"
    );
}

#[test]
fn test_to_json_single_line() {
    let stats = RunStatistics::new(SolveMode::Smt, "done", Duration::from_millis(100));
    let json_str = stats.to_json();
    assert!(
        !json_str.contains('\n'),
        "JSON stats should be a single line for easy grep/parse"
    );
}

#[test]
fn test_to_json_all_modes() {
    for (mode, expected) in [
        (SolveMode::Smt, "smt"),
        (SolveMode::DimacsSat, "dimacs-sat"),
        (SolveMode::Chc, "chc"),
        (SolveMode::Portfolio, "portfolio"),
        (SolveMode::Pb, "pb"),
    ] {
        let stats = RunStatistics::new(mode, "unknown", Duration::ZERO);
        let json_str = stats.to_json();
        let parsed: serde_json::Value = serde_json::from_str(&json_str).unwrap();
        assert_eq!(parsed["mode"], expected);
    }
}

#[test]
fn test_stats_config_any() {
    assert!(!StatsConfig {
        human: false,
        full: false,
        json: false
    }
    .any());
    assert!(StatsConfig {
        human: true,
        full: false,
        json: false
    }
    .any());
    assert!(StatsConfig {
        human: false,
        full: false,
        json: true
    }
    .any());
    assert!(StatsConfig {
        human: true,
        full: false,
        json: true
    }
    .any());
}

/// Curated output is a strict SELECTION of the full block, never a rewrite of
/// it. Every key the curated block prints must appear in the full block with
/// the same spelling — otherwise `--stats-full` has stopped being the superset
/// the flag promises, and a script that greps a curated key off default `-st`
/// would be reading a name that exists nowhere else.
///
/// The two documented additions are exempt by name, so adding a third one
/// silently is what this test is really guarding against.
#[test]
fn every_curated_key_also_appears_in_the_full_block() {
    const ADDED_BY_CURATION: [&str; 2] = [":result", ":total-time"];

    // Both branches matter: several full-block rows are conditional, so an
    // empty run and a populated one can select different key sets.
    let empty = ay_dpll::Statistics::default();

    let mut populated = ay_dpll::Statistics::default();
    // Certificate counters live in `extra` and render only when present.
    populated.set_int("cert.decisions", 1);
    populated.set_int("cert.proof_steps_recorded", 1);
    // The full block gates the term rows on this being non-zero.
    populated.term_bytes = 939;
    populated.term_count = 6;

    // A third branch: the curated `quantifiers` group is whole-group
    // conditional and re-selects the E-matching pair, which the full block
    // gates separately. Both gate combinations have to stay subsets.
    let mut quantified = ay_dpll::Statistics::default();
    quantified.ematching_rounds_completed = 2;
    quantified.ematching_instances_created = 4;
    quantified.quantifier_cegqi_rounds = 3;

    // …and the case where the lane engaged with NO completed E-matching round,
    // which is exactly where a careless curated row would name a key the full
    // block omitted.
    let mut cegqi_only = ay_dpll::Statistics::default();
    cegqi_only.quantifier_cegqi_ce_lemmas = 9;

    for stats in [&empty, &populated, &quantified, &cegqi_only] {
        let full = stats.to_string();
        let curated = curated_smt_statistics(stats, "sat", Duration::from_millis(58), false);

        for line in curated.lines() {
            let Some(key) = line.split_whitespace().next() else {
                continue;
            };
            if !key.starts_with(':') || ADDED_BY_CURATION.contains(&key) {
                continue;
            }
            assert!(
                full.contains(&format!("{key} ")),
                "curated key {key} is absent from the full block, so --stats-full is no longer a superset"
            );
        }
    }
}

/// The verdict and the wall clock are the two things the block never stated,
/// and `:total-time` is z3's spelling for the latter. `:time` is the solver's
/// own time and must survive alongside it rather than be replaced by it.
#[test]
fn curated_block_states_the_verdict_and_both_clocks() {
    let stats = ay_dpll::Statistics::default();
    let curated = curated_smt_statistics(&stats, "unsat", Duration::from_millis(58), false);
    assert!(curated.contains(":result"), "{curated}");
    assert!(curated.contains("unsat"), "{curated}");
    assert!(
        curated.contains(":total-time                      0.058"),
        "{curated}"
    );
    assert!(curated.contains(":time "), "{curated}");
}

/// `-st` is z3's spelling, and z3 prints four resource rows on every run:
/// `:time`, `:memory`, `:max-memory` and `:rlimit-count`. Curation kept the
/// first three and dropped the deterministic one, so a caller comparing ay's
/// `-st` with z3's found that meter only under `--stats-full`. Each must
/// survive curation with the full block's value.
#[test]
fn curated_block_keeps_z3s_four_resource_rows() {
    let mut stats = ay_dpll::Statistics::default();
    stats.rlimit_count = 97;
    let curated = curated_smt_statistics(&stats, "sat", Duration::ZERO, false);
    for key in [":time", ":memory", ":max-memory", ":rlimit-count"] {
        assert!(
            curated
                .lines()
                .any(|line| line.split_whitespace().next() == Some(key)),
            "missing z3 resource row {key} in:\n{curated}"
        );
    }
    assert!(
        curated
            .lines()
            .any(|line| line.split_whitespace().collect::<Vec<_>>() == [":rlimit-count", "97"]),
        "the curated :rlimit-count must carry the counter's value:\n{curated}"
    );
    assert!(
        stats.to_string().contains(":rlimit-count 97"),
        "the full block must carry the same value, or curation invented it"
    );
}

/// Group labels are a terminal affordance. Redirected `-st` must stay a
/// comment-free s-expression, because that is what anything parsing it expects.
#[test]
fn group_comments_are_terminal_only() {
    let stats = ay_dpll::Statistics::default();
    let piped = curated_smt_statistics(&stats, "sat", Duration::ZERO, false);
    let terminal = curated_smt_statistics(&stats, "sat", Duration::ZERO, true);

    assert!(!piped.contains(';'), "{piped}");
    assert!(terminal.contains("  ; search\n"), "{terminal}");
    assert!(terminal.starts_with("(:statistics\n") && terminal.ends_with(')'));
    // The labels are the only difference: strip them and the two agree.
    let stripped: String = terminal
        .lines()
        .filter(|line| !line.trim_start().starts_with(';'))
        .map(|line| format!("{line}\n"))
        .collect();
    assert_eq!(
        stripped.trim_end_matches('\n'),
        piped.trim_end_matches('\n')
    );
}

/// A counter that is absent means "this run minted none", which is not the same
/// claim as a zero. Certificate rows come from `extra` and must stay omitted
/// rather than be fabricated.
#[test]
fn absent_certificate_counters_are_omitted_not_zeroed() {
    let stats = ay_dpll::Statistics::default();
    let curated = curated_smt_statistics(&stats, "sat", Duration::ZERO, false);
    assert!(!curated.contains(":cert.decisions"), "{curated}");
}

/// The quantifier group is whole-group conditional. A QF run that never touched
/// a binder must not gain nine rows about quantifier instantiation; a run that
/// did must see the instantiation count on default `-st` rather than only under
/// `--stats-full`, which is what made the parity census read the full block.
#[test]
fn quantifier_group_is_conditional_but_complete_once_it_fires() {
    let idle = ay_dpll::Statistics::default();
    let curated = curated_smt_statistics(&idle, "sat", Duration::ZERO, false);
    assert!(!curated.contains(":quantifier."), "{curated}");
    assert!(!curated.contains(":ematching-"), "{curated}");

    let mut engaged = ay_dpll::Statistics::default();
    engaged.ematching_rounds_completed = 2;
    engaged.ematching_instances_created = 4;
    let curated = curated_smt_statistics(&engaged, "unknown", Duration::ZERO, false);
    for key in [
        ":ematching-rounds-completed",
        ":ematching-instances-created",
        ":quantifier.proxies_minted",
        ":quantifier.guarded_instances_created",
        ":quantifier.guarded_instances_asserted",
        ":quantifier.mbqi.rounds",
        ":quantifier.mbqi.candidates_probed",
        ":quantifier.cegqi.rounds",
        ":quantifier.cegqi.ce_lemmas",
    ] {
        assert!(curated.contains(key), "missing {key} in:\n{curated}");
    }
    // Zeros are printed once the group fires: "wired and idle" is a different
    // claim from "not wired", and the staged work is measured on the difference.
    assert!(curated.contains(":quantifier.proxies_minted"), "{curated}");
    assert!(
        curated
            .lines()
            .any(|l| l.contains(":quantifier.proxies_minted") && l.trim_end().ends_with(" 0")),
        "{curated}"
    );
}

/// The quantified routes record their verdicts, refusals and parked
/// certificates in `extra`. `-st` prints exactly the keys present under the
/// three route prefixes, with the full block's value, and nothing on a run the
/// routes never touched.
#[test]
fn quantified_route_rows_follow_extra_exactly() {
    let idle = ay_dpll::Statistics::default();
    let curated = curated_smt_statistics(&idle, "sat", Duration::ZERO, true);
    assert!(!curated.contains("quantified routes"), "{curated}");
    assert!(!curated.contains(":qsat."), "{curated}");

    let mut engaged = ay_dpll::Statistics::default();
    engaged.extra.insert(
        "qsat.publish".to_string(),
        ay_dpll::StatValue::String("unsat-expansion-refused".to_string()),
    );
    engaged
        .extra
        .insert("qlra.cert_steps".to_string(), ay_dpll::StatValue::Int(45));
    engaged
        .extra
        .insert("qlra.seconds".to_string(), ay_dpll::StatValue::Float(2.5));
    engaged.extra.insert(
        "eq_qe.gate".to_string(),
        ay_dpll::StatValue::String("refused".to_string()),
    );
    engaged
        .extra
        .insert("qsatx.unrelated".to_string(), ay_dpll::StatValue::Int(1));
    let curated = curated_smt_statistics(&engaged, "unknown", Duration::ZERO, false);
    let full = engaged.to_string();
    for key in [
        ":qsat.publish",
        ":qlra.cert_steps",
        ":qlra.seconds",
        ":eq_qe.gate",
    ] {
        let row = curated
            .lines()
            .find(|line| line.split_whitespace().next() == Some(key))
            .unwrap_or_else(|| panic!("missing {key} in:\n{curated}"));
        let value = row.split_whitespace().nth(1).expect("row has a value");
        assert!(
            full.contains(&format!("{key} {value}")),
            "curated {key} {value} differs from the full block:\n{full}"
        );
    }
    assert!(!curated.contains(":qsatx."), "{curated}");
}
